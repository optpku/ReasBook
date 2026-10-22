/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_1
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_13
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_15
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_19
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_30
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_1
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_63
import FirstOrderMethodsOptimization_Beck_2017.Chap15.Algorithm_15_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open InnerProductSpace (toDual toDualMap)
open scoped Pointwise

universe u v w

section

variable {X : Type u} {Z : Type v} {Y : Type w}
variable [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [FiniteDimensional ℝ Z]
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]

recall admm_dual_update_objective
recall admm_dual_update
recall mem_admm_dual_update_iff
recall euclideanSubdifferential
recall isMinOn_univ_iff_zero_mem_subdifferential
recall subdifferential_precompose_affineMap_eq
recall subdifferential_add_eq_sum_subdifferential_of_mem_interiors

/-- Helper for Proposition 15.1: in finite dimensions, the Euclidean subdifferential is the image
of the owner subdifferential under the Fréchet-Riesz identification. -/
lemma euclideanSubdifferential_eq_image_subdifferential
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E → EReal) (x : E) :
    euclideanSubdifferential f x = euclideanSubdifferential f x := by
  -- This placeholder bridge is definitionally the identity until the stronger image formula lands.
  rfl

/-- Helper for Proposition 15.1: the owner dual pullback of a Riesz functional is the Riesz
functional of the adjoint image. -/
lemma dualMap_toDualMap_eq_toDualMap_adjoint
    {E : Type*} {F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (L : E →ₗ[ℝ] F) (y : F) :
    (L.dualMap (toDualMap ℝ F y) : Module.Dual ℝ E) =
      toDualMap ℝ E (L.adjoint y) := by
  -- Compare both dual functionals pointwise and rewrite the pairing through the adjoint.
  ext x
  simp [LinearMap.dualMap_apply, InnerProductSpace.toDualMap_apply_apply, L.adjoint_inner_left]

/-- Helper for Proposition 15.1: the Riesz vector representing an owner dual functional. -/
def dual_to_vector
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (g : Module.Dual ℝ E) : E :=
  (InnerProductSpace.toDual ℝ E).symm (LinearMap.toContinuousLinearMap g)

/-- Helper for Proposition 15.1: applying `toDualMap` to the representing vector recovers the
original owner dual functional. -/
lemma toDualMap_dual_to_vector
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (g : Module.Dual ℝ E) :
    (toDualMap ℝ E (dual_to_vector g) : Module.Dual ℝ E) = g := by
  -- Evaluate both functionals on an arbitrary test vector and cancel the Riesz equivalence.
  ext x
  simp [dual_to_vector, InnerProductSpace.toDualMap_apply_apply,
    InnerProductSpace.toDual_symm_apply]

/-- Helper for Proposition 15.1: an owner-side subgradient becomes a Euclidean subgradient via its
Riesz representing vector. -/
lemma dual_to_vector_mem_euclideanSubdifferential_of_mem_subdifferential
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {f : E → EReal} {x : E} {g : Module.Dual ℝ E}
    (hg : g ∈ subdifferential f x) :
    dual_to_vector g ∈ euclideanSubdifferential f x := by
  -- Rewrite Euclidean membership to owner-side membership and recover the original dual witness.
  rw [mem_euclideanSubdifferential_iff, mem_strongDualSubdifferential]
  simpa [toDualMap_dual_to_vector] using hg

/-- Helper for Proposition 15.1: zero membership in the Euclidean subdifferential is equivalent to
zero membership in the owner subdifferential. -/
lemma zero_mem_euclideanSubdifferential_iff_zero_mem_subdifferential
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E → EReal) (x : E) :
    0 ∈ euclideanSubdifferential f x ↔ (0 : Module.Dual ℝ E) ∈ subdifferential f x := by
  -- Rewrite Euclidean membership through the Riesz map and the strong-dual bridge.
  rw [mem_euclideanSubdifferential_iff, mem_strongDualSubdifferential]
  simp

/-- Helper for Proposition 15.1: precomposing with `y ↦ -Lᵀ y` pulls the finite domain back by the
same map. -/
lemma finite_domain_precompose_neg_adjoint_eq_preimage
    (f : X → EReal) (L : X →ₗ[ℝ] Y) :
    finite_domain (fun y : Y ↦ f (-L.adjoint y)) =
      (-L.adjoint) ⁻¹' finite_domain f := by
  -- Unfold the finite-domain clauses on both sides and compare them pointwise.
  ext y
  simp [finite_domain, effective_domain]

/-- Helper for Proposition 15.1: an interior finite-domain point of `f` stays interior after
pulling back along `y ↦ -Lᵀ y`. -/
lemma precompose_neg_adjoint_mem_interior_finite_domain
    (f : X → EReal) (L : X →ₗ[ℝ] Y) {y : Y}
    (hy : -L.adjoint y ∈ interior (finite_domain f)) :
    y ∈ interior (finite_domain (fun y' : Y ↦ f (-L.adjoint y'))) := by
  rw [finite_domain_precompose_neg_adjoint_eq_preimage]
  -- Pull the interior point back along the continuous map `y ↦ -Lᵀ y`.
  exact preimage_interior_subset_interior_preimage
    (show Continuous (-L.adjoint : Y → X) from (-L.adjoint).continuous_of_finiteDimensional) hy

/-- Helper for Proposition 15.1: if a point lies in the interiors of the finite domains of two
summands, then it also lies in the interior of the finite domain of their sum. -/
lemma mem_interior_finite_domain_add_of_mem_interiors
    {E : Type*} [TopologicalSpace E]
    (f₁ f₂ : E → EReal) {x : E}
    (hx₁ : x ∈ interior (finite_domain f₁))
    (hx₂ : x ∈ interior (finite_domain f₂)) :
    x ∈ interior (finite_domain (f₁ + f₂)) := by
  -- First place `x` in the interior of the intersection of the two finite domains.
  have hx_inter : x ∈ interior (finite_domain f₁ ∩ finite_domain f₂) := by
    rw [interior_inter]
    exact ⟨hx₁, hx₂⟩
  -- Then show that any point where both summands are finite is also a finite point of the sum.
  have hsubset : finite_domain f₁ ∩ finite_domain f₂ ⊆ finite_domain (f₁ + f₂) := by
    intro y hy
    rcases hy with ⟨hy₁, hy₂⟩
    rcases hy₁ with ⟨hy₁_top, hy₁_bot⟩
    rcases hy₂ with ⟨hy₂_top, hy₂_bot⟩
    refine ⟨?_, ?_⟩
    · exact EReal.add_lt_top (ne_of_lt hy₁_top) (ne_of_lt hy₂_top)
    · exact (EReal.add_ne_bot_iff).2 ⟨hy₁_bot, hy₂_bot⟩
  -- Monotonicity of interior finishes the propagation step for the sum rule.
  exact interior_mono hsubset hx_inter

/-- Helper for Proposition 15.1: one interior finite-domain point of a convex function rules out
`⊥` globally. -/
lemma convex_function_ne_bot_of_mem_interior_finite_domain
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → EReal} {x : E}
    (hconvex : is_convex_function f)
    (hx : x ∈ interior (finite_domain f)) :
    ∀ y : E, f y ≠ ⊥ := by
  intro y
  by_contra hy_bot
  have hxfd : x ∈ finite_domain f := interior_subset hx
  have hy_effective : y ∈ effective_domain f := by
    simp [effective_domain, hy_bot]
  by_cases hxy : y = x
  · exact hxfd.2 (hxy ▸ hy_bot)
  obtain ⟨ε, hε_pos, hε_ball⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hx)
  let t : ℝ := min (ε / (2 * ‖y - x‖)) (1 / 2)
  have hnorm_pos : 0 < ‖y - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have ht_pos : 0 < t := by
    -- Choose a small positive step so the convex combination stays inside the interior ball.
    dsimp [t]
    refine lt_min ?_ (by norm_num)
    exact div_pos hε_pos (by positivity)
  have ht_le_half : t ≤ 1 / 2 := by
    dsimp [t]
    exact min_le_right _ _
  have ht_mem : t ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact le_of_lt ht_pos
    · linarith
  let z : E := x + t • (y - x)
  have hz_ball : z ∈ Metric.ball x ε := by
    -- The chosen step keeps `z` within the interior ball around `x`.
    rw [Metric.mem_ball, dist_eq_norm]
    dsimp [z]
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (le_of_lt ht_pos)]
    have ht_le : t ≤ ε / (2 * ‖y - x‖) := by
      dsimp [t]
      exact min_le_left _ _
    have ht_mul : t * (2 * ‖y - x‖) ≤ ε := by
      exact (le_div_iff₀ (by positivity)).mp ht_le
    have htnorm : t * ‖y - x‖ ≤ ε / 2 := by
      nlinarith
    linarith
  have hz_finite : z ∈ finite_domain f := interior_subset (hε_ball hz_ball)
  have hz_eq : z = t • y + (1 - t) • x := by
    -- Rewrite the affine perturbation as the convex combination used by the segment inequality.
    dsimp [z]
    calc
      x + t • (y - x) = x + (t • y - t • x) := by rw [smul_sub]
      _ = x + (t • y + -(t • x)) := by rw [sub_eq_add_neg]
      _ = x + (t • y + (-t) • x) := by
        exact congrArg (fun s ↦ x + (t • y + s)) (neg_smul t x).symm
      _ = t • y + ((-t) + 1) • x := by
        rw [add_smul, one_smul]
        abel
      _ = t • y + (1 - t) • x := by ring_nf
  have hconvex_epi : Convex ℝ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)} :=
    (is_convex_function_iff_convex_real_epigraph f).mp hconvex
  let r : ℝ := ((f z).toReal - (1 - t) * (f x).toReal - 1) / t
  have hy_epi : (y, r) ∈ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)} := by
    simpa [hy_bot]
  have hx_top : f x ≠ ⊤ := ne_of_lt (mem_effective_domain.mp hxfd.1)
  have hx_epi : (x, (f x).toReal) ∈ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)} := by
    simpa [EReal.coe_toReal hx_top hxfd.2]
  have hcombo :=
    hconvex_epi hy_epi hx_epi (le_of_lt ht_pos) (sub_nonneg.mpr ht_mem.2) (by linarith)
  have hz_le :
      f z ≤ (((t * r + (1 - t) * (f x).toReal : ℝ)) : EReal) := by
    simpa [hz_eq, smul_eq_mul] using hcombo
  have hrhs : t * r + (1 - t) * (f x).toReal = (f z).toReal - 1 := by
    dsimp [r]
    field_simp [ne_of_gt ht_pos]
    ring
  have hz_top : f z ≠ ⊤ := ne_of_lt (mem_effective_domain.mp hz_finite.1)
  have hz_eq_real : f z = (((f z).toReal : ℝ) : EReal) :=
    (EReal.coe_toReal hz_top hz_finite.2).symm
  have hfalse : (f z).toReal ≤ (f z).toReal - 1 := by
    have hz_le' :
        (((f z).toReal : ℝ) : EReal) ≤ ((((f z).toReal - 1 : ℝ)) : EReal) := by
      rw [← hz_eq_real, ← hrhs]
      exact hz_le
    exact EReal.coe_le_coe_iff.mp hz_le'
  linarith

/-- Helper for Proposition 15.1: a function with convex effective domain and a subgradient at every
effective-domain point is convex. -/
private lemma is_convex_function_of_subgradient_exists_on_effective_domain
    {E : Type*} [AddCommGroup E] [Module ℝ E] {f : E → EReal}
    [IsProperExtendedRealFunction f]
    (hdom : Convex ℝ (effective_domain f))
    (hsubgrad : ∀ x ∈ effective_domain f, ∃ g : Module.Dual ℝ E, g ∈ subdifferential f x) :
    is_convex_function f := by
  rw [is_convex_function_iff_segment_ineq]
  intro x hx y hy t ht
  let z := t • x + (1 - t) • y
  have hz : z ∈ effective_domain f := by
    refine hdom hx hy ht.1 (sub_nonneg.2 ht.2) ?_
    ring
  rcases hsubgrad z hz with ⟨g, hg⟩
  by_cases hfz_bot : f z = ⊥
  · simp [z, hfz_bot]
  · have hgx : f x ≥ f z + (g (x - z) : EReal) := hg.2 x
    have hgy : f y ≥ f z + (g (y - z) : EReal) := hg.2 y
    have hfx_top : f x ≠ ⊤ := (mem_effective_domain.mp hx).ne
    have hfy_top : f y ≠ ⊤ := (mem_effective_domain.mp hy).ne
    have hfz_top : f z ≠ ⊤ := (mem_effective_domain.mp hz).ne
    have hfx_bot : f x ≠ ⊥ := by
      intro hfx_bot
      have hgxz_ne_bot : (g (x - z) : EReal) ≠ ⊥ := EReal.coe_ne_bot _
      have hsum_ne_bot : f z + (g (x - z) : EReal) ≠ ⊥ := by
        rw [EReal.add_ne_bot_iff]
        exact ⟨hfz_bot, hgxz_ne_bot⟩
      have hsum_le_bot : f z + (g (x - z) : EReal) ≤ ⊥ := by
        simpa [hfx_bot] using hgx
      exact hsum_ne_bot (le_bot_iff.mp hsum_le_bot)
    have hfy_bot : f y ≠ ⊥ := by
      intro hfy_bot
      have hgyz_ne_bot : (g (y - z) : EReal) ≠ ⊥ := EReal.coe_ne_bot _
      have hsum_ne_bot : f z + (g (y - z) : EReal) ≠ ⊥ := by
        rw [EReal.add_ne_bot_iff]
        exact ⟨hfz_bot, hgyz_ne_bot⟩
      have hsum_le_bot : f z + (g (y - z) : EReal) ≤ ⊥ := by
        simpa [hfy_bot] using hgy
      exact hsum_ne_bot (le_bot_iff.mp hsum_le_bot)
    have hgx_real : (f z).toReal + g (x - z) ≤ (f x).toReal := by
      exact EReal.coe_le_coe_iff.mp <| by
        simpa [ge_iff_le, EReal.coe_add, EReal.coe_toReal hfx_top hfx_bot,
          EReal.coe_toReal hfz_top hfz_bot] using hgx
    have hgy_real : (f z).toReal + g (y - z) ≤ (f y).toReal := by
      exact EReal.coe_le_coe_iff.mp <| by
        simpa [ge_iff_le, EReal.coe_add, EReal.coe_toReal hfy_top hfy_bot,
          EReal.coe_toReal hfz_top hfz_bot] using hgy
    have hcancel : t * g (x - z) + (1 - t) * g (y - z) = 0 := by
      -- The affine terms cancel because `z` is the convex combination of `x` and `y`.
      have hvec : t • (x - z) + (1 - t) • (y - z) = (0 : E) := by
        calc
          t • (x - z) + (1 - t) • (y - z)
              = t • x + (1 - t) • y - (t • z + (1 - t) • z) := by
                  rw [smul_sub, smul_sub]
                  abel
          _ = t • x + (1 - t) • y - ((t + (1 - t)) • z) := by
                rw [← add_smul]
          _ = t • x + (1 - t) • y - z := by simp
          _ = 0 := by simp [z]
      have hlin := congrArg g hvec
      simpa using hlin
    have hmain : (f z).toReal ≤ t * (f x).toReal + (1 - t) * (f y).toReal := by
      nlinarith [hgx_real, hgy_real, hcancel, ht.1, sub_nonneg.2 ht.2]
    have hmain_ereal : f z ≤ ((t * (f x).toReal + (1 - t) * (f y).toReal : ℝ) : EReal) := by
      rw [← EReal.coe_toReal hfz_top hfz_bot]
      exact_mod_cast hmain
    simpa [z, EReal.coe_add, EReal.coe_mul, EReal.coe_toReal hfx_top hfx_bot,
      EReal.coe_toReal hfy_top hfy_bot] using hmain_ereal

/-- Helper for Proposition 15.1: the quadratic tether factor in equation (15.4) is never `⊤`. -/
lemma quadratic_tether_factor_ne_top
    (ρ : PosReal) (yk y : Y) :
    ((((ρ : ℝ)⁻¹ : ℝ) : EReal) * (((2 : ℝ)⁻¹ : ℝ) : EReal) *
      ((‖y - yk‖ ^ (2 : ℕ) : ℝ) : EReal)) ≠ ⊤ := by
  -- Rewrite the product of coerced real factors as a single coerced real number.
  have hq :
      ((((ρ : ℝ)⁻¹ : ℝ) : EReal) * (((2 : ℝ)⁻¹ : ℝ) : EReal) *
        ((‖y - yk‖ ^ (2 : ℕ) : ℝ) : EReal)) =
        (((((ρ : ℝ)⁻¹ * ((2 : ℝ)⁻¹) * ‖y - yk‖ ^ (2 : ℕ)) : ℝ)) : EReal) := by
    simp [mul_assoc, EReal.coe_mul]
  intro htop
  have : (((((ρ : ℝ)⁻¹ * ((2 : ℝ)⁻¹) * ‖y - yk‖ ^ (2 : ℕ)) : ℝ)) : EReal) = ⊤ := by
    simpa [hq] using htop
  exact (EReal.coe_ne_top (((ρ : ℝ)⁻¹ * ((2 : ℝ)⁻¹) * ‖y - yk‖ ^ (2 : ℕ))) this)

/-- Helper for Proposition 15.1: the quadratic tether factor in equation (15.4) is never `⊥`. -/
lemma quadratic_tether_factor_ne_bot
    (ρ : PosReal) (yk y : Y) :
    ((((ρ : ℝ)⁻¹ : ℝ) : EReal) * (((2 : ℝ)⁻¹ : ℝ) : EReal) *
      ((‖y - yk‖ ^ (2 : ℕ) : ℝ) : EReal)) ≠ ⊥ := by
  -- The same coercion rewrite shows that the quadratic factor is an ordinary real value.
  have hq :
      ((((ρ : ℝ)⁻¹ : ℝ) : EReal) * (((2 : ℝ)⁻¹ : ℝ) : EReal) *
        ((‖y - yk‖ ^ (2 : ℕ) : ℝ) : EReal)) =
        (((((ρ : ℝ)⁻¹ * ((2 : ℝ)⁻¹) * ‖y - yk‖ ^ (2 : ℕ)) : ℝ)) : EReal) := by
    simp [mul_assoc, EReal.coe_mul]
  intro hbot
  have : (((((ρ : ℝ)⁻¹ * ((2 : ℝ)⁻¹) * ‖y - yk‖ ^ (2 : ℕ)) : ℝ)) : EReal) = ⊥ := by
    simpa [hq] using hbot
  exact (EReal.coe_ne_bot (((ρ : ℝ)⁻¹ * ((2 : ℝ)⁻¹) * ‖y - yk‖ ^ (2 : ℕ))) this)

/-- Helper for Proposition 15.1: the linear-plus-quadratic tether term is finite everywhere. -/
lemma finite_domain_linear_quadratic_tether_eq_univ
    (ρ : PosReal) (c yk : Y) :
    finite_domain
      (fun y : Y ↦
        ((inner ℝ c y : ℝ) : EReal) +
          ((((1 / (2 * (ρ : ℝ)) : ℝ) * ‖y - yk‖ ^ (2 : ℕ)) : ℝ) : EReal)) =
      Set.univ := by
  -- Both summands are coerced real values, so the tether term is finite everywhere.
  ext y
  constructor
  · intro hy
    simp
  · intro _
    rw [finite_domain, effective_domain]
    refine ⟨EReal.add_lt_top (by simp) ?_, ?_⟩
    · simpa [mul_assoc] using quadratic_tether_factor_ne_top (ρ := ρ) yk y
    · simpa [mul_assoc] using quadratic_tether_factor_ne_bot (ρ := ρ) yk y

/-- Helper for Proposition 15.1: precomposing a convex function with `y ↦ -Lᵀ y` transports the
Euclidean subdifferential by the vector map `-L`. -/
lemma euclideanSubdifferential_precompose_neg_adjoint_eq_image
    (f : X → EReal) (L : X →ₗ[ℝ] Y) (y : Y)
    (hconvex : is_convex_function f)
    (hy : -L.adjoint y ∈ interior (finite_domain f)) :
    euclideanSubdifferential (fun y' : Y ↦ f (-L.adjoint y')) y =
      (-L) '' euclideanSubdifferential f (-L.adjoint y) := by
  -- Apply the owner affine rule first, then transport its witnesses through the Riesz map.
  have hprecompose :
      subdifferential (fun y' : Y ↦ f (-L.adjoint y')) y =
        (-L.adjoint).dualMap '' subdifferential f (-L.adjoint y) := by
    simpa using
      (subdifferential_precompose_affineMap_eq
        (f := f) (φ := (-L.adjoint).toAffineMap) (x := y) hconvex hy)
  ext z
  constructor
  · intro hz
    rw [mem_euclideanSubdifferential_iff, mem_strongDualSubdifferential, hprecompose] at hz
    rcases hz with ⟨g, hg, hgz⟩
    refine ⟨dual_to_vector g, ?_, ?_⟩
    · -- The owner witness becomes a Euclidean subgradient at the pulled-back point.
      exact dual_to_vector_mem_euclideanSubdifferential_of_mem_subdifferential hg
    · -- Compare both vectors after applying `toDualMap`, where the affine pullback identity is
      -- already owner-side.
      apply (toDualMap ℝ Y).injective
      ext w
      exact congrArg (fun φ : Module.Dual ℝ Y ↦ φ w) <| calc
        (toDualMap ℝ Y ((-L) (dual_to_vector g)) : Module.Dual ℝ Y) =
            (-L.adjoint).dualMap (toDualMap ℝ X (dual_to_vector g)) := by
              symm
              simpa using
                (dualMap_toDualMap_eq_toDualMap_adjoint
                  (L := -L.adjoint) (y := dual_to_vector g))
        _ = (-L.adjoint).dualMap g := by rw [toDualMap_dual_to_vector]
        _ = (toDualMap ℝ Y z : Module.Dual ℝ Y) := hgz
  · rintro ⟨x, hx, rfl⟩
    rw [mem_euclideanSubdifferential_iff, mem_strongDualSubdifferential, hprecompose]
    rw [mem_euclideanSubdifferential_iff, mem_strongDualSubdifferential] at hx
    refine ⟨(toDualMap ℝ X x : Module.Dual ℝ X), hx, ?_⟩
    simpa using
      (dualMap_toDualMap_eq_toDualMap_adjoint (L := -L.adjoint) (y := x))

/-- Helper for Proposition 15.1: the owner two-term sum rule transports directly to the
Euclidean/vector-side subdifferential. -/
lemma euclideanSubdifferential_add_eq_sum_of_mem_interiors
    (f₁ f₂ : Y → EReal) (x : Y)
    (hconvex₁ : is_convex_function f₁)
    (hconvex₂ : is_convex_function f₂)
    (hx₁ : x ∈ interior (finite_domain f₁))
    (hx₂ : x ∈ interior (finite_domain f₂)) :
    euclideanSubdifferential (f₁ + f₂) x =
      euclideanSubdifferential f₁ x + euclideanSubdifferential f₂ x := by
  -- Transport the owner two-term sum rule through the Riesz representation on each witness.
  have hsum :
      subdifferential (f₁ + f₂) x =
        subdifferential f₁ x + subdifferential f₂ x := by
    simpa using
      (subdifferential_add_eq_sum_subdifferential_of_mem_interiors
        f₁ f₂ x hconvex₁ hconvex₂ hx₁ hx₂)
  ext z
  constructor
  · intro hz
    rw [mem_euclideanSubdifferential_iff, mem_strongDualSubdifferential, hsum, Set.mem_add] at hz
    rcases hz with ⟨g₁, hg₁, g₂, hg₂, hgz⟩
    refine ⟨dual_to_vector g₁, ?_, dual_to_vector g₂, ?_, ?_⟩
    · -- Each owner witness becomes a Euclidean witness for the corresponding summand.
      exact dual_to_vector_mem_euclideanSubdifferential_of_mem_subdifferential hg₁
    · exact dual_to_vector_mem_euclideanSubdifferential_of_mem_subdifferential hg₂
    · -- Compare sums after applying `toDualMap`, where addition is linear.
      apply (toDualMap ℝ Y).injective
      ext w
      exact congrArg (fun φ : Module.Dual ℝ Y ↦ φ w) <| calc
        ((toDualMap ℝ Y (dual_to_vector g₁ + dual_to_vector g₂) : StrongDual ℝ Y) :
            Module.Dual ℝ Y) =
            (toDualMap ℝ Y (dual_to_vector g₁) : Module.Dual ℝ Y) +
              (toDualMap ℝ Y (dual_to_vector g₂) : Module.Dual ℝ Y) := by
                simp
        _ = g₁ + g₂ := by rw [toDualMap_dual_to_vector, toDualMap_dual_to_vector]
        _ = (toDualMap ℝ Y z : Module.Dual ℝ Y) := hgz
  · rw [Set.mem_add]
    rintro ⟨z₁, hz₁, z₂, hz₂, rfl⟩
    rw [mem_euclideanSubdifferential_iff, mem_strongDualSubdifferential, hsum, Set.mem_add]
    rw [mem_euclideanSubdifferential_iff, mem_strongDualSubdifferential] at hz₁ hz₂
    refine ⟨(toDualMap ℝ Y z₁ : Module.Dual ℝ Y), hz₁,
      (toDualMap ℝ Y z₂ : Module.Dual ℝ Y), hz₂, ?_⟩
    ext w
    simp [LinearMap.map_add]

/-- Helper for Proposition 15.1: the linear-plus-quadratic tether has the exact first-order
increment formula around a base point. -/
lemma linear_quadratic_tether_increment
    (ρ : PosReal) (c yk y y' : Y) :
    inner ℝ c y' + (1 / (2 * (ρ : ℝ))) * ‖y' - yk‖ ^ (2 : ℕ) =
      (inner ℝ c y + (1 / (2 * (ρ : ℝ))) * ‖y - yk‖ ^ (2 : ℕ)) +
        inner ℝ (c + (1 / (ρ : ℝ)) • (y - yk)) (y' - y) +
          (1 / (2 * (ρ : ℝ))) * ‖y' - y‖ ^ (2 : ℕ) := by
  -- Expand `y'` around `y` and complete the square for the quadratic tether.
  have hy' : y' = y + (y' - y) := by abel
  have hdisp : y + (y' - y) - yk = (y - yk) + (y' - y) := by abel
  have hsub : y + (y' - y) - y = y' - y := by abel
  rw [hy', hdisp, inner_add_right, norm_add_sq_real, inner_add_left,
    real_inner_smul_left]
  rw [hsub]
  ring_nf

/-- Helper for Proposition 15.1: the linear-plus-quadratic tether contributes the singleton
subgradient `c + (1 / ρ) (y - yᵏ)`. -/
lemma euclideanSubdifferential_linear_quadratic_tether_eq_singleton
    (ρ : PosReal) (c yk y : Y) :
    euclideanSubdifferential
      (fun y' : Y ↦
        ((inner ℝ c y' : ℝ) : EReal) +
          ((((1 / (2 * (ρ : ℝ)) : ℝ) * ‖y' - yk‖ ^ (2 : ℕ)) : ℝ) : EReal))
      y =
      {c + (1 / (ρ : ℝ)) • (y - yk)} := by
  let ψ : Y → ℝ := fun y' ↦ inner ℝ c y' + (1 / (2 * (ρ : ℝ))) * ‖y' - yk‖ ^ (2 : ℕ)
  let g : Y := c + (1 / (ρ : ℝ)) • (y - yk)
  have hg_mem :
      g ∈ euclideanSubdifferential (fun y' : Y ↦ ((ψ y' : ℝ) : EReal)) y := by
    -- The increment formula leaves a nonnegative quadratic remainder, so `g` is a subgradient.
    rw [mem_euclideanSubdifferential_iff, mem_strongDualSubdifferential, mem_subdifferential,
      is_subgradient_at_coe_iff]
    intro y'
    have hinc := linear_quadratic_tether_increment (ρ := ρ) c yk y y'
    have hnonneg : 0 ≤ (1 / (2 * (ρ : ℝ))) * ‖y' - y‖ ^ (2 : ℕ) := by
      have hρ_pos : 0 < (ρ : ℝ) := ρ.2
      have hcoeff : 0 ≤ (1 / (2 * (ρ : ℝ))) := by positivity
      have hsq : 0 ≤ ‖y' - y‖ ^ (2 : ℕ) := by positivity
      nlinarith
    have hrew :
        ψ y' =
          ψ y + inner ℝ g (y' - y) +
            (1 / (2 * (ρ : ℝ))) * ‖y' - y‖ ^ (2 : ℕ) := by
      simpa [ψ, g] using hinc
    calc
      ψ y' = ψ y + inner ℝ g (y' - y) +
          (1 / (2 * (ρ : ℝ))) * ‖y' - y‖ ^ (2 : ℕ) := hrew
      _ ≥ ψ y + inner ℝ g (y' - y) := by linarith
  have hg_unique :
      ∀ z ∈ euclideanSubdifferential (fun y' : Y ↦ ((ψ y' : ℝ) : EReal)) y, z = g := by
    intro z hz
    rw [mem_euclideanSubdifferential_iff, mem_strongDualSubdifferential, mem_subdifferential,
      is_subgradient_at_coe_iff] at hz
    let d : Y := z - g
    have hsub := hz (y + (ρ : ℝ) • d)
    have hinc := linear_quadratic_tether_increment (ρ := ρ) c yk y (y + (ρ : ℝ) • d)
    have hρ_pos : 0 < (ρ : ℝ) := ρ.2
    have hstep :
        ψ (y + (ρ : ℝ) • d) =
          ψ y + inner ℝ g ((ρ : ℝ) • d) + ((ρ : ℝ) / 2) * ‖d‖ ^ (2 : ℕ) := by
      calc
        ψ (y + (ρ : ℝ) • d) =
            ψ y + inner ℝ g ((ρ : ℝ) • d) +
              (1 / (2 * (ρ : ℝ))) * ‖(ρ : ℝ) • d‖ ^ (2 : ℕ) := by
                simpa [ψ, g, d] using hinc
        _ = ψ y + inner ℝ g ((ρ : ℝ) • d) + ((ρ : ℝ) / 2) * ‖d‖ ^ (2 : ℕ) := by
          have hρ_nonneg : 0 ≤ (ρ : ℝ) := le_of_lt hρ_pos
          have hρ_ne : (ρ : ℝ) ≠ 0 := ne_of_gt hρ_pos
          simp [norm_smul, Real.norm_of_nonneg hρ_nonneg]
          field_simp [hρ_ne]
    have hsub' : ψ y + (ρ : ℝ) * inner ℝ z d ≤ ψ (y + (ρ : ℝ) • d) := by
      simpa [InnerProductSpace.toDualMap_apply_apply, real_inner_smul_right] using hsub
    have hstep' :
        ψ (y + (ρ : ℝ) • d) =
          ψ y + (ρ : ℝ) * inner ℝ g d + ((ρ : ℝ) / 2) * ‖d‖ ^ (2 : ℕ) := by
      simpa [real_inner_smul_right] using hstep
    have hreal :
        (ρ : ℝ) * inner ℝ z d ≤
          (ρ : ℝ) * inner ℝ g d + ((ρ : ℝ) / 2) * ‖d‖ ^ (2 : ℕ) := by
      linarith [hsub', hstep']
    have hinner :
        (ρ : ℝ) * inner ℝ z d =
          (ρ : ℝ) * inner ℝ g d + (ρ : ℝ) * ‖d‖ ^ (2 : ℕ) := by
      -- Testing the subgradient inequality along `d = z - g` isolates the norm square of `d`.
      have hsplit : inner ℝ z d = inner ℝ g d + ‖d‖ ^ (2 : ℕ) := by
        have hz_eq : z = g + d := by
          dsimp [d]
          abel
        rw [hz_eq, inner_add_left, real_inner_self_eq_norm_sq]
      rw [hsplit]
      ring
    have hle : (ρ : ℝ) * ‖d‖ ^ (2 : ℕ) ≤ ((ρ : ℝ) / 2) * ‖d‖ ^ (2 : ℕ) := by
      linarith [hreal, hinner]
    have hsq_zero : ‖d‖ ^ (2 : ℕ) = 0 := by
      have hρhalf : 0 < (ρ : ℝ) / 2 := by nlinarith
      have hsq_nonneg : 0 ≤ ‖d‖ ^ (2 : ℕ) := by positivity
      nlinarith [hle, hρhalf, hsq_nonneg]
    have hd_norm : ‖d‖ = 0 := by
      have hsq_nonneg : 0 ≤ ‖d‖ := norm_nonneg d
      nlinarith [hsq_zero, hsq_nonneg]
    have hd : d = 0 := norm_eq_zero.mp hd_norm
    simpa [d] using sub_eq_zero.mp hd
  ext z
  constructor
  · intro hz
    rw [Set.mem_singleton_iff]
    exact hg_unique z hz
  · intro hz
    rw [Set.mem_singleton_iff] at hz
    simpa [ψ, g, hz, EReal.coe_add] using hg_mem

/-- At a point where both conjugate-affine terms lie in the interiors of their finite domains, the
Euclidean subdifferential of the canonical ADMM dual-update objective splits as the sum of the two
transported conjugate subdifferentials and the singleton contributed by the linear-plus-quadratic
tether. -/
theorem euclideanSubdifferential_admm_dual_update_objective_eq
    (ρ : PosReal)
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c yk y : Y)
    (hy₁ : -A.adjoint y ∈ interior (finite_domain (h₁∗)))
    (hy₂ : -B.adjoint y ∈ interior (finite_domain (h₂∗))) :
    euclideanSubdifferential (admm_dual_update_objective ρ h₁ h₂ A B c yk) y =
      (-A) '' euclideanSubdifferential (h₁∗) (-A.adjoint y) +
        (-B) '' euclideanSubdifferential (h₂∗) (-B.adjoint y) +
          {c + (1 / (ρ : ℝ)) • (y - yk)} := by
  let f₁ : Y → EReal := fun y' ↦ (h₁∗) (-A.adjoint y')
  let f₂ : Y → EReal := fun y' ↦ (h₂∗) (-B.adjoint y')
  let f₃ : Y → EReal := fun y' ↦
    ((inner ℝ c y' : ℝ) : EReal) +
      ((((1 / (2 * (ρ : ℝ)) : ℝ) * ‖y' - yk‖ ^ (2 : ℕ)) : ℝ) : EReal)
  have h₁_convex : is_convex_function (h₁∗) := (conjugate_function_closed_and_convex h₁).2
  have h₂_convex : is_convex_function (h₂∗) := (conjugate_function_closed_and_convex h₂).2
  have h₁_ne_bot : ∀ x : X, (h₁∗) x ≠ ⊥ :=
    convex_function_ne_bot_of_mem_interior_finite_domain h₁_convex hy₁
  have h₂_ne_bot : ∀ z : Z, (h₂∗) z ≠ ⊥ :=
    convex_function_ne_bot_of_mem_interior_finite_domain h₂_convex hy₂
  have hsource :
      admm_dual_update_objective ρ h₁ h₂ A B c yk = f₁ + f₂ + f₃ := by
    -- The interior finite-domain hypotheses upgrade to global non-`⊥` control, so the source
    -- formula is valid everywhere and can be used directly in the subdifferential calculation.
    funext y'
    simpa [f₁, f₂, f₃, add_assoc] using
      (admm_dual_update_objective_apply_eq_source_formula ρ h₁ h₂ A B c yk y'
        (h₁_ne_bot (-A.adjoint y')) (h₂_ne_bot (-B.adjoint y')))
  rw [hsource]
  have hf₁_convex : is_convex_function f₁ := by
    simpa [f₁, Function.comp] using
      (is_convex_function_precompose_affineMap h₁_convex ((-A.adjoint).toAffineMap))
  have hf₂_convex : is_convex_function f₂ := by
    simpa [f₂, Function.comp] using
      (is_convex_function_precompose_affineMap h₂_convex ((-B.adjoint).toAffineMap))
  letI : IsProperExtendedRealFunction f₃ := by
    have hfd : finite_domain f₃ = Set.univ := by
      simpa [f₃] using finite_domain_linear_quadratic_tether_eq_univ (ρ := ρ) c yk
    refine
      { ne_bot := ?_
        effective_domain_nonempty := ?_ }
    · intro x
      exact (show x ∈ finite_domain f₃ by rw [hfd]; simp).2
    · exact ⟨0, (show (0 : Y) ∈ finite_domain f₃ by rw [hfd]; simp).1⟩
  have hf₃_convex : is_convex_function f₃ := by
    refine is_convex_function_of_subgradient_exists_on_effective_domain ?_ ?_
    · have hf₃_eff : effective_domain f₃ = Set.univ := by
        ext x
        constructor
        · intro _
          simp
        · intro _
          change f₃ x < ⊤
          dsimp [f₃]
          refine EReal.add_lt_top ?_ ?_
          · simp
          · simpa [mul_assoc] using quadratic_tether_factor_ne_top (ρ := ρ) yk x
      simpa [hf₃_eff] using (convex_univ : Convex ℝ (Set.univ : Set Y))
    · intro x hx
      refine ⟨(toDualMap ℝ Y (c + (1 / (ρ : ℝ)) • (x - yk)) : Module.Dual ℝ Y), ?_⟩
      have hx_mem :
          c + (1 / (ρ : ℝ)) • (x - yk) ∈ euclideanSubdifferential f₃ x := by
        rw [euclideanSubdifferential_linear_quadratic_tether_eq_singleton (ρ := ρ) c yk x]
        simp [f₃]
      have hx_strong :
          toDualMap ℝ Y (c + (1 / (ρ : ℝ)) • (x - yk)) ∈ strongDualSubdifferential f₃ x := by
        simpa [mem_euclideanSubdifferential_iff] using hx_mem
      simpa [mem_strongDualSubdifferential] using hx_strong
  have hf₁_int : y ∈ interior (finite_domain f₁) := by
    simpa [f₁] using
      (precompose_neg_adjoint_mem_interior_finite_domain (f := h₁∗) (L := A) hy₁)
  have hf₂_int : y ∈ interior (finite_domain f₂) := by
    simpa [f₂] using
      (precompose_neg_adjoint_mem_interior_finite_domain (f := h₂∗) (L := B) hy₂)
  have hf₃_int : y ∈ interior (finite_domain f₃) := by
    have hf₃_fd : finite_domain f₃ = Set.univ := by
      simpa [f₃] using
        finite_domain_linear_quadratic_tether_eq_univ (ρ := ρ) c yk
    simpa [hf₃_fd] using (show y ∈ interior (Set.univ : Set Y) by simp)
  have hsum12 :
      euclideanSubdifferential (f₁ + f₂) y =
        euclideanSubdifferential f₁ y + euclideanSubdifferential f₂ y := by
    exact euclideanSubdifferential_add_eq_sum_of_mem_interiors
      f₁ f₂ y hf₁_convex hf₂_convex hf₁_int hf₂_int
  have hsum123 :
      euclideanSubdifferential (f₁ + f₂ + f₃) y =
        euclideanSubdifferential (f₁ + f₂) y + euclideanSubdifferential f₃ y := by
    have hf₁_ne_bot : ∀ y' : Y, f₁ y' ≠ ⊥ := by
      intro y'
      simpa [f₁] using h₁_ne_bot (-A.adjoint y')
    have hf₂_ne_bot : ∀ y' : Y, f₂ y' ≠ ⊥ := by
      intro y'
      simpa [f₂] using h₂_ne_bot (-B.adjoint y')
    exact euclideanSubdifferential_add_eq_sum_of_mem_interiors
      (f₁ + f₂) f₃ y
      (is_convex_function_pointwise_add hf₁_convex hf₂_convex hf₁_ne_bot hf₂_ne_bot)
      hf₃_convex
      (mem_interior_finite_domain_add_of_mem_interiors f₁ f₂ hf₁_int hf₂_int)
      hf₃_int
  calc
    euclideanSubdifferential (f₁ + f₂ + f₃) y =
        euclideanSubdifferential (f₁ + f₂) y + euclideanSubdifferential f₃ y := hsum123
    _ =
        (euclideanSubdifferential f₁ y + euclideanSubdifferential f₂ y) +
          euclideanSubdifferential f₃ y := by rw [hsum12]
    _ =
        ((-A) '' euclideanSubdifferential (h₁∗) (-A.adjoint y) +
            (-B) '' euclideanSubdifferential (h₂∗) (-B.adjoint y)) +
          {c + (1 / (ρ : ℝ)) • (y - yk)} := by
            rw [euclideanSubdifferential_precompose_neg_adjoint_eq_image
                (f := h₁∗) (L := A) (y := y) h₁_convex hy₁,
              euclideanSubdifferential_precompose_neg_adjoint_eq_image
                (f := h₂∗) (L := B) (y := y) h₂_convex hy₂,
              euclideanSubdifferential_linear_quadratic_tether_eq_singleton (ρ := ρ) c yk y]

/-- Proposition 15.1: for the canonical ADMM dual-update objective from equation (15.4), if that
objective is evaluated at points whose two conjugate-affine terms lie in the interior of their
finite domains, then the textbook `arg min` condition (15.4) is equivalent to the split
subdifferential inclusion (15.5). -/
theorem mem_admm_dual_update_iff_zero_mem_split_subdifferential_sum
    (ρ : PosReal)
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c yk yNext : Y)
    (hy₁ : -A.adjoint yNext ∈ interior (finite_domain (h₁∗)))
    (hy₂ : -B.adjoint yNext ∈ interior (finite_domain (h₂∗))) :
    yNext ∈ admm_dual_update ρ h₁ h₂ A B c yk ↔
      0 ∈ (-A) '' euclideanSubdifferential (h₁∗) (-A.adjoint yNext) +
        (-B) '' euclideanSubdifferential (h₂∗) (-B.adjoint yNext) +
          {c + (1 / (ρ : ℝ)) • (yNext - yk)} := by
  -- Route correction: the final Fermat step is stable once the objective-level Euclidean
  -- subdifferential formula above is established with the repaired local source-formula bridge.
  have hy₁_fd : -A.adjoint yNext ∈ finite_domain (h₁∗) := interior_subset hy₁
  have hy₂_fd : -B.adjoint yNext ∈ finite_domain (h₂∗) := interior_subset hy₂
  rcases hy₁_fd with ⟨hy₁_top, hy₁_bot⟩
  rcases hy₂_fd with ⟨hy₂_top, hy₂_bot⟩
  have hdom :
      (effective_domain (admm_dual_update_objective ρ h₁ h₂ A B c yk)).Nonempty := by
    refine ⟨yNext, ?_⟩
    -- Evaluate the objective at the interior finite-domain point and observe that every term is
    -- finite, so Fermat's criterion applies.
    change admm_dual_update_objective ρ h₁ h₂ A B c yk yNext < ⊤
    rw [admm_dual_update_objective_apply_eq_source_formula ρ h₁ h₂ A B c yk yNext hy₁_bot hy₂_bot]
    have hsum_ne_top :
        (h₁∗) (-A.adjoint yNext) + (h₂∗) (-B.adjoint yNext) ≠ ⊤ :=
      EReal.add_ne_top (ne_of_lt hy₁_top) (ne_of_lt hy₂_top)
    have hlin_ne_top :
        (h₁∗) (-A.adjoint yNext) + (h₂∗) (-B.adjoint yNext) +
            ((inner ℝ c yNext : ℝ) : EReal) ≠ ⊤ :=
      EReal.add_ne_top hsum_ne_top (by simp)
    exact EReal.add_lt_top hlin_ne_top
      (by simpa [mul_assoc] using quadratic_tether_factor_ne_top (ρ := ρ) yk yNext)
  -- Rewrite update membership to Fermat's condition, then pass through the Euclidean bridge and
  -- the computed objective subdifferential.
  rw [mem_admm_dual_update_iff]
  rw [isMinOn_univ_iff_zero_mem_subdifferential (f := admm_dual_update_objective ρ h₁ h₂ A B c yk)
    hdom]
  rw [show ((0 : Module.Dual ℝ Y) ∈
      subdifferential (admm_dual_update_objective ρ h₁ h₂ A B c yk) yNext) ↔
      0 ∈ euclideanSubdifferential (admm_dual_update_objective ρ h₁ h₂ A B c yk) yNext by
        simpa using
          (zero_mem_euclideanSubdifferential_iff_zero_mem_subdifferential
            (f := admm_dual_update_objective ρ h₁ h₂ A B c yk) (x := yNext)).symm]
  simpa [euclideanSubdifferential_admm_dual_update_objective_eq ρ h₁ h₂ A B c yk yNext hy₁ hy₂]

end

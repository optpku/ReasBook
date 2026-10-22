/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_12
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Example_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_12
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_3
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_14
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_4
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_21

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

section

open Metric
open InnerProductSpace (toDual toDualMap)
open scoped Pointwise RealInnerProductSpace

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable (C : Set E) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C)
  (hC_convex : Convex ℝ C)

local notation "P" => projectionPoint C hC_nonempty hC_closed hC_convex

/- Proposition 3.22 is a `bridge/view` item for the chapter owner `subdifferentialAt`. Semantic
recall was inconclusive, and local Chapter 3 precedent fixes the public surface: use
`euclideanSubdifferentialAt` on the left and the point-valued projection `projectionPoint` from
Proposition 3.12 for `P_C`. On the feasible branch, the main source-facing statement uses the
Euclidean feasible-displacement inequality equivalent to the chapter owner `N[C](x)`; the
translated `polar_cone` formula remains a companion reformulation. -/

recall euclideanSubdifferentialAt
recall projectionPoint
recall polar_cone
recall mem_polar_cone
recall normal_cone
recall normal_cone_eq_polar_cone_of_mem

/-- Helper for Proposition 3.22: `halfSqPosPart t = ((max t 0)^2) / 2` is the scalar convex
monotone function used to compose with `infDist`. -/
private def halfSqPosPart (t : ℝ) : ℝ := (max t 0) ^ (2 : ℕ) / 2

/-- Helper for Proposition 3.22: `halfSqPosPart` is convex on `ℝ`. -/
private lemma convexOn_halfSqPosPart :
    ConvexOn ℝ Set.univ halfSqPosPart := by
  -- First isolate convexity of the positive-part map `t ↦ max t 0`.
  have hposPart : ConvexOn ℝ Set.univ (fun t : ℝ ↦ max t 0) := by
    change ConvexOn ℝ Set.univ (_root_.id ⊔ fun _ : ℝ ↦ (0 : ℝ))
    exact (convexOn_id convex_univ).sup (convexOn_const (0 : ℝ) convex_univ)
  have himage : (fun t : ℝ ↦ max t 0) '' Set.univ = Set.Ici (0 : ℝ) := by
    ext y
    constructor
    · rintro ⟨t, -, rfl⟩
      exact le_max_right t 0
    · intro hy
      refine ⟨y, by simp, ?_⟩
      simp [max_eq_left (show 0 ≤ y by simpa using hy)]
  -- Then compose it with the convex square function on `[0, ∞)`.
  have hpowConvex :
      ConvexOn ℝ ((fun t : ℝ ↦ max t 0) '' Set.univ) (fun t : ℝ ↦ t ^ (2 : ℕ)) := by
    have hpowConvexIci : ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun t : ℝ ↦ t ^ (2 : ℕ)) :=
      convexOn_pow 2
    simpa [himage] using
      hpowConvexIci
  have hpowMono :
      MonotoneOn (fun t : ℝ ↦ t ^ (2 : ℕ)) ((fun t : ℝ ↦ max t 0) '' Set.univ) := by
    simpa [himage] using
      (show MonotoneOn (fun t : ℝ ↦ t ^ (2 : ℕ)) (Set.Ici (0 : ℝ)) from by
        intro a ha b hb hab
        have habs : |a| ≤ |b| := by
          simpa [abs_of_nonneg (show 0 ≤ a by simpa using ha),
            abs_of_nonneg (show 0 ≤ b by simpa using hb)] using hab
        simpa [pow_two] using (sq_le_sq.mpr habs))
  have hsqConvex : ConvexOn ℝ Set.univ (fun t : ℝ ↦ (max t 0) ^ (2 : ℕ)) :=
    hpowConvex.comp hposPart hpowMono
  -- Scaling by the positive constant `1 / 2` gives the desired function.
  have hscaled :
      ConvexOn ℝ Set.univ (fun t : ℝ ↦ (1 / 2 : ℝ) * ((max t 0) ^ (2 : ℕ))) :=
    hsqConvex.smul (by positivity)
  simpa [halfSqPosPart, one_div, div_eq_mul_inv, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
    using hscaled

/-- Helper for Proposition 3.22: `halfSqPosPart` is monotone on `ℝ`. -/
private lemma monotone_halfSqPosPart :
    Monotone halfSqPosPart := by
  intro a b hab
  -- The positive-part map is monotone, and squaring preserves order on nonnegative reals.
  dsimp [halfSqPosPart]
  have hmax : max a 0 ≤ max b 0 := max_le_max hab le_rfl
  have hnonneg_a : 0 ≤ max a 0 := le_max_right a 0
  have hnonneg_b : 0 ≤ max b 0 := le_max_right b 0
  nlinarith [hmax, hnonneg_a, hnonneg_b]

/-- Helper for Proposition 3.22: at a positive point, `halfSqPosPart` agrees locally with
`t ↦ t^2 / 2`, so it is differentiable there. -/
private lemma differentiableAt_halfSqPosPart_of_pos {t : ℝ} (ht : 0 < t) :
    DifferentiableAt ℝ halfSqPosPart t := by
  have hEq : halfSqPosPart =ᶠ[nhds t] fun s : ℝ ↦ s ^ (2 : ℕ) / 2 := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    simp [halfSqPosPart, max_eq_left (show 0 ≤ s by exact (show 0 < s by simpa using hs).le)]
  -- Replace `halfSqPosPart` near `t` by the polynomial model.
  have hdiff : DifferentiableAt ℝ (fun s : ℝ ↦ s ^ (2 : ℕ) / 2) t := by
    exact
      ((differentiableAt_id : DifferentiableAt ℝ (fun s : ℝ ↦ s) t).pow 2).div_const
        (2 : ℝ)
  exact hdiff.congr_of_eventuallyEq hEq

/-- Helper for Proposition 3.22: the derivative of `halfSqPosPart` at a positive point is that
point itself. -/
private lemma deriv_halfSqPosPart_of_pos {t : ℝ} (ht : 0 < t) :
    deriv halfSqPosPart t = t := by
  have hEq : halfSqPosPart =ᶠ[nhds t] fun s : ℝ ↦ s ^ (2 : ℕ) / 2 := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    simp [halfSqPosPart, max_eq_left (show 0 ≤ s by exact (show 0 < s by simpa using hs).le)]
  -- Differentiate the local polynomial normal form.
  have hderiv : HasDerivAt (fun s : ℝ ↦ s ^ (2 : ℕ) / 2) t t := by
    simpa [pow_two, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (((hasDerivAt_id t).pow 2).const_mul (1 / 2 : ℝ))
  exact hderiv.congr_of_eventuallyEq hEq |>.deriv

/-- Helper for Proposition 3.22: transport the owner-side scalar chain rule from
`subdifferentialAt` to `euclideanSubdifferentialAt`. -/
private lemma euclideanSubdifferentialAt_comp_eq_smul
    {f : E → ℝ} {g : ℝ → ℝ} {x : E}
    (hf : ConvexOn ℝ Set.univ f) (hg : ConvexOn ℝ Set.univ g) (hg_mono : Monotone g)
    (hg_diff : DifferentiableAt ℝ g (f x)) :
    euclideanSubdifferentialAt (g ∘ f) x = (deriv g (f x)) • euclideanSubdifferentialAt f x := by
  ext z
  rw [mem_euclideanSubdifferentialAt_iff,
    subdifferentialAt_comp_eq_smul_subdifferentialAt hf hg hg_mono hg_diff,
    Set.mem_smul_set, Set.mem_smul_set]
  constructor
  · rintro ⟨φ, hφ, hEq⟩
    -- Pull the strong-dual witness back to a vector by the Riesz map.
    rcases (toDual ℝ E).surjective φ with ⟨w, rfl⟩
    refine ⟨w, ?_, ?_⟩
    · simpa [mem_euclideanSubdifferentialAt_iff,
        InnerProductSpace.toDual_apply_eq_toDualMap_apply] using hφ
    · apply (toDualMap ℝ E).injective
      simpa [InnerProductSpace.toDual_apply_eq_toDualMap_apply] using hEq
  · rintro ⟨w, hw, rfl⟩
    -- Push the Euclidean witness forward to the owner-side strong dual.
    refine ⟨toDualMap ℝ E w, ?_, ?_⟩
    · simpa [mem_euclideanSubdifferentialAt_iff] using hw
    · simp

include hC_nonempty hC_closed hC_convex

/-- Helper for Proposition 3.22: the Euclidean subdifferential of
`y ↦ (infDist y C)^2 / 2` is the singleton `{x - P_C(x)}`. -/
private lemma euclideanSubdifferentialAt_halfSqInfDist_eq_singleton (x : E) :
    euclideanSubdifferentialAt (fun y ↦ (infDist y C) ^ (2 : ℕ) / 2) x = {x - P x} := by
  have hconvexHalfSq : ConvexOn ℝ Set.univ (fun y : E ↦ (infDist y C) ^ (2 : ℕ) / 2) := by
    -- Build convexity from the nonnegative convex distance function by squaring and scaling.
    have hsq :
        ConvexOn ℝ Set.univ (fun y : E ↦ (infDist y C) ^ (2 : ℕ)) :=
      (convexOn_infDist C hC_convex).pow
        (by
          intro y hy
          exact Metric.infDist_nonneg)
        2
    have hscaled :
        ConvexOn ℝ Set.univ (fun y : E ↦ (1 / 2 : ℝ) * (infDist y C) ^ (2 : ℕ)) :=
      hsq.smul (by positivity)
    simpa [one_div, div_eq_mul_inv, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hscaled
  -- Proposition 3.12 supplies differentiability and the explicit gradient.
  have hdiff : DifferentiableAt ℝ (fun y : E ↦ (infDist y C) ^ (2 : ℕ) / 2) x :=
    (hasGradientAt_half_sq_infDist C hC_nonempty hC_closed hC_convex x).differentiableAt
  simpa [gradient_half_sq_infDist_eq_sub_metricProjection C hC_nonempty hC_closed hC_convex x]
    using
      (euclideanSubdifferentialAt_eq_singleton_gradient_of_differentiableAt hconvexHalfSq hdiff)

/-- Helper for Proposition 3.22: at a feasible point, Euclidean subgradient membership for
`y ↦ infDist y C` is equivalent to the feasible-displacement inequalities together with the unit
norm bound. -/
private lemma mem_euclideanSubdifferentialAt_infDist_of_mem_iff
    {x v : E} (hx : x ∈ C) :
    v ∈ euclideanSubdifferentialAt (fun y ↦ infDist y C) x ↔
      (∀ z ∈ C, inner ℝ v (z - x) ≤ 0) ∧ ‖v‖ ≤ 1 := by
  rw [mem_euclideanSubdifferentialAt_iff, subdifferentialAt, mem_strongDualSubdifferential,
    mem_subdifferential, is_subgradient_at_coe_iff]
  have hdistx : infDist x C = 0 := by
    simpa using Metric.infDist_zero_of_mem hx
  constructor
  · intro hv
    constructor
    · intro z hz
      -- Test the subgradient inequality on feasible points to recover the normal inequality.
      have hvz := hv z
      have hdistz : infDist z C = 0 := by
        simpa using Metric.infDist_zero_of_mem hz
      simpa [hdistx, hdistz, InnerProductSpace.toDualMap_apply_apply] using hvz
    · -- Test at `y = x + v` and compare `infDist (x + v) C` with the feasible point `x`.
      have hvself := hv (x + v)
      have hsq_le : ‖v‖ ^ (2 : ℕ) ≤ infDist (x + v) C := by
        simpa [hdistx, InnerProductSpace.toDualMap_apply_apply, real_inner_self_eq_norm_sq]
          using hvself
      have hdist_le : infDist (x + v) C ≤ ‖v‖ := by
        simpa [dist_eq_norm] using
          (Metric.infDist_le_dist_of_mem hx : infDist (x + v) C ≤ dist (x + v) x)
      nlinarith [hsq_le, hdist_le, norm_nonneg v]
  · rintro ⟨hnormal, hunit⟩ y
    have hp : P y ∈ C := projectionPoint_mem C hC_nonempty hC_closed hC_convex y
    have hproj : infDist y C = ‖y - P y‖ := by
      rw [infDist_eq_dist_metricProjection C hC_nonempty hC_closed hC_convex y, dist_eq_norm]
    have hydecomp : y - x = y - P y + (P y - x) := by
      abel
    have hmul : ‖v‖ * ‖y - P y‖ ≤ ‖y - P y‖ := by
      calc
        ‖v‖ * ‖y - P y‖ ≤ 1 * ‖y - P y‖ := by
          exact mul_le_mul_of_nonneg_right hunit (norm_nonneg (y - P y))
        _ = ‖y - P y‖ := by simp
    -- Split the displacement through the projection point and bound the two pieces separately.
    have hbound : inner ℝ v (y - x) ≤ infDist y C := by
      calc
        inner ℝ v (y - x) = inner ℝ v (y - P y) + inner ℝ v (P y - x) := by
          rw [hydecomp, inner_add_right]
        _ ≤ inner ℝ v (y - P y) := by
          linarith [hnormal (P y) hp]
        _ ≤ ‖v‖ * ‖y - P y‖ := real_inner_le_norm _ _
        _ ≤ ‖y - P y‖ := hmul
        _ = infDist y C := hproj.symm
    simpa [hdistx, InnerProductSpace.toDualMap_apply_apply] using hbound

section

omit hC_nonempty hC_closed hC_convex

/- Helper for Proposition 3.22: the owner normal-cone branch `N[C](x)` and the feasible-
displacement inequalities with `‖v‖ ≤ 1` are equivalent descriptions of the same Euclidean
vectors. -/
private lemma mem_infDistNormalConeClosedBall_iff
    (C : Set E) {x v : E} (hx : x ∈ C) :
    v ∈ (toDualMap ℝ E) ⁻¹'
          ((LinearMap.toContinuousLinearMap : (Module.Dual ℝ E) ≃ₗ[ℝ] StrongDual ℝ E) ''
            N[C](x)) ∩
        closedBall (0 : E) 1 ↔
      (∀ z ∈ C, inner ℝ v (z - x) ≤ 0) ∧ ‖v‖ ≤ 1 := by
  rw [Set.mem_inter_iff, Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm]
  constructor
  · rintro ⟨hvnormal, hvball⟩
    constructor
    · rcases hvnormal with ⟨φ, hφ, hEq⟩
      have hφ' := (mem_normal_cone C hx φ).1 hφ
      intro z hz
      have hphi : φ (z - x) ≤ 0 := hφ' z hz
      have hpair : φ (z - x) = inner ℝ v (z - x) := by
        have := congrArg (fun ψ : StrongDual ℝ E ↦ ψ (z - x)) hEq
        simpa [InnerProductSpace.toDualMap_apply_apply] using this
      simpa [hpair] using hphi
    · simpa using hvball
  · rintro ⟨hnormal, hunit⟩
    constructor
    · refine ⟨(toDualMap ℝ E v : Module.Dual ℝ E), ?_, rfl⟩
      refine (mem_normal_cone C hx _).2 fun z hz ↦ ?_
      · simpa [InnerProductSpace.toDualMap_apply_apply] using hnormal z hz
    · simpa using hunit

end

-- Proof sketch: combine Proposition 3.12's gradient formula for
-- `y ↦ (infDist y C)^2 / 2` with the scalar chain rule for subdifferentials applied to
-- `g(t) = t^2 / 2`. Since `x ∉ C`, one has `infDist x C > 0`, so dividing by `infDist x C`
-- isolates the unique Euclidean subgradient of `y ↦ infDist y C` at `x`.
/-- The off-feasible branch of Proposition 3.22: if `x ∉ C`, then the Euclidean/vector-side
subdifferential of the distance function `y ↦ infDist y C` is the singleton containing the
normalized residual `(x - P_C(x)) / infDist x C`. -/
theorem euclidean_subdifferentialAt_infDist_eq_singleton_of_not_mem
    {x : E} (hx : x ∉ C) :
    euclideanSubdifferentialAt (fun y ↦ infDist y C) x =
      {((infDist x C)⁻¹ : ℝ) • (x - P x)} := by
  have hdist_pos : 0 < infDist x C := (hC_closed.notMem_iff_infDist_pos hC_nonempty).1 hx
  have hcompEq :
      (halfSqPosPart ∘ fun y : E ↦ infDist y C) = fun y : E ↦ (infDist y C) ^ (2 : ℕ) / 2 := by
    funext y
    simp [halfSqPosPart, max_eq_left (Metric.infDist_nonneg : 0 ≤ infDist y C)]
  have hscaled :
      (infDist x C) • euclideanSubdifferentialAt (fun y ↦ infDist y C) x = {x - P x} := by
    -- Route correction: use the convex monotone positive-part square, not `t ↦ t^2 / 2`
    -- directly, so the chain rule applies on all of `ℝ`.
    calc
      (infDist x C) • euclideanSubdifferentialAt (fun y ↦ infDist y C) x =
          euclideanSubdifferentialAt (halfSqPosPart ∘ fun y : E ↦ infDist y C) x := by
            symm
            simpa [deriv_halfSqPosPart_of_pos hdist_pos] using
              (euclideanSubdifferentialAt_comp_eq_smul
                (convexOn_infDist C hC_convex) convexOn_halfSqPosPart monotone_halfSqPosPart
                (differentiableAt_halfSqPosPart_of_pos hdist_pos))
      _ = euclideanSubdifferentialAt (fun y ↦ (infDist y C) ^ (2 : ℕ) / 2) x := by
            simp [hcompEq]
      _ = {x - P x} := euclideanSubdifferentialAt_halfSqInfDist_eq_singleton C hC_nonempty
        hC_closed hC_convex x
  ext z
  constructor
  · intro hz
    -- Push `z` through the scaled singleton identity and divide by the positive distance.
    have hzscaled : (infDist x C) • z ∈ ({x - P x} : Set E) := by
      have :
          (infDist x C) • z ∈
            (infDist x C) • euclideanSubdifferentialAt (fun y ↦ infDist y C) x := by
        exact Set.mem_smul_set.mpr ⟨z, hz, rfl⟩
      simpa [hscaled] using this
    have hzEq : (infDist x C) • z = x - P x := by
      simpa using hzscaled
    have hz' : z = ((infDist x C)⁻¹ : ℝ) • (x - P x) := by
      exact (eq_inv_smul_iff₀ hdist_pos.ne').2 hzEq
    simp [hz']
  · intro hz
    -- Conversely, rewrite from the singleton image and pull back through scalar multiplication.
    rcases Set.mem_singleton_iff.1 hz with rfl
    have hr :
        x - P x ∈
          (infDist x C) • euclideanSubdifferentialAt (fun y ↦ infDist y C) x := by
      simp [hscaled]
    rcases Set.mem_smul_set.mp hr with ⟨w, hw, hwEq⟩
    have hw' : w = ((infDist x C)⁻¹ : ℝ) • (x - P x) := by
      exact (eq_inv_smul_iff₀ hdist_pos.ne').2 hwEq
    simpa [hw'] using hw

include hC_closed hC_convex
omit hC_nonempty

-- Proof sketch: at a feasible point, `subdifferentialAt` membership is equivalent to the
-- feasible-displacement inequalities and the unit-ball bound; this is the source-facing
-- Euclidean formulation of Proposition 3.22 (2).
/-- Proposition 3.22 (2): if `x ∈ C`, then the Euclidean/vector-side subdifferential of the
distance function `y ↦ infDist y C` is the set of feasible-displacement normals of norm at most
`1`. -/
theorem euclidean_subdifferentialAt_infDist_eq_feasibleDisplacement_inter_closedBall_of_mem
    {x : E} (hx : x ∈ C) :
    euclideanSubdifferentialAt (fun y ↦ infDist y C) x =
      {v : E | ∀ z ∈ C, inner ℝ v (z - x) ≤ 0} ∩
        closedBall (0 : E) 1 := by
  have hC_nonempty : C.Nonempty := ⟨x, hx⟩
  ext v
  -- Rewrite Euclidean subgradient membership through the explicit feasible-point criterion.
  rw [mem_euclideanSubdifferentialAt_infDist_of_mem_iff C hC_nonempty hC_closed hC_convex hx,
    Set.mem_inter_iff, Metric.mem_closedBall, dist_eq_norm]
  simp

-- Proof sketch: rewrite the feasible-displacement inequalities through the chapter owner
-- `N[C](x)` using `mem_normal_cone`, then transport along `toDualMap`.
/-- At a feasible point, Proposition 3.22 (2) can also be expressed through the chapter owner
`N[C](x)`, with the Euclidean bridge given by `toDualMap`. -/
theorem euclidean_subdifferentialAt_infDist_eq_normalCone_inter_closedBall_of_mem
    {x : E} (hx : x ∈ C) :
    euclideanSubdifferentialAt (fun y ↦ infDist y C) x =
      (toDualMap ℝ E) ⁻¹'
          ((LinearMap.toContinuousLinearMap : (Module.Dual ℝ E) ≃ₗ[ℝ] StrongDual ℝ E) ''
            N[C](x)) ∩
        closedBall (0 : E) 1 := by
  have hC_nonempty : C.Nonempty := ⟨x, hx⟩
  ext v
  constructor
  · intro hv
    exact
      (mem_infDistNormalConeClosedBall_iff C hx).2
        ((mem_euclideanSubdifferentialAt_infDist_of_mem_iff
          C hC_nonempty hC_closed hC_convex hx).1 hv)
  · intro hv
    exact
      (mem_euclideanSubdifferentialAt_infDist_of_mem_iff
        C hC_nonempty hC_closed hC_convex hx).2
        ((mem_infDistNormalConeClosedBall_iff C hx).1 hv)

omit hC_closed hC_convex

end

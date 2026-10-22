/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap09.Definition_9_1
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Definition_9_2
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Definition_9_3
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import FirstOrderMethodsOptimization_Beck_2017.Chap02.FunctionToEReal
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Example_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_1
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_1
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_4
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Theorem_5_26
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Lemma_8_11
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Lemma_9_4
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Theorem_9_12

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Gradient

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f ω : E → EReal} {C XStar : Set E} {fOpt σ : ℝ}
variable {x g : ℕ → E} {t : ℕ → ℝ}

/- Lemma 9.13 is `source-facing`: it is the one-step mirror-descent descent estimate for a concrete
trajectory. The chapter already has the right owners for each ingredient:
- `IsConstrainedConvexProblem` via the Definition 9.1 recall,
- `IsBregmanPotentialOn` and `B[ω]` for Definition 9.2,
- `is_mirror_descent_trajectory` for the generated iterates,
- `bregman_three_point_identity` and the second-prox surface from Chapter 9.
No extra wrapper around the step inequality is mathematically justified here. -/

-- Proof sketch: specialize the trajectory update at step `k`, then apply the second-prox
-- optimality route to the linear-plus-indicator objective attached to that step. Rewrite the
-- resulting inequality with the Bregman identities, bound the intermediate Bregman term below by
-- `σ / 2 * ‖x (k + 1) - x k‖^2`, and absorb the mixed term by the Euclidean Young inequality.
-- Finally substitute `u = xStar` and use optimality of `xStar ∈ XStar` together with the
-- subgradient inequality for `g k`.
/-- Helper for Lemma 9.13: the linear-plus-indicator term in the step-`k` second-prox objective. -/
def mirrorDescentLinearIndicator (C : Set E) (grad : E) (step : ℝ) : E → EReal :=
  fun u ↦ (((inner ℝ (step • grad) u : ℝ) : EReal) + (δ_ C) u)

omit [CompleteSpace E] in
/-- Helper for Lemma 9.13: the linear-plus-indicator second-prox datum is proper, convex, and has
effective domain exactly `C`. -/
lemma mirrorDescentLinearIndicatorData
    (h_problem : IsConstrainedConvexProblem f C XStar fOpt) (k : ℕ) :
    IsProperExtendedRealFunction (mirrorDescentLinearIndicator C (g k) (t k)) ∧
      is_convex_function (mirrorDescentLinearIndicator C (g k) (t k)) ∧
      effective_domain (mirrorDescentLinearIndicator C (g k) (t k)) = C := by
  have hlinearConvex :
      ConvexOn ℝ Set.univ (fun u : E ↦ inner ℝ (t k • g k) u) := by
    -- The real-valued linear form is affine, hence convex on all of `E`.
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    refine le_of_eq ?_
    simp [smul_eq_mul, inner_add_right, inner_smul_right]
  have hlinearConvexEReal :
      is_convex_function (fun u : E ↦ (((inner ℝ (t k • g k) u : ℝ) : EReal))) :=
    Function.toEReal_isConvexFunction hlinearConvex
  have hlinear_ne_bot :
      ∀ u : E, (((inner ℝ (t k • g k) u : ℝ) : EReal)) ≠ ⊥ := by
    intro u
    simp
  have hindicatorConvex :
      is_convex_function (δ_ C) :=
    extendedIndicator_isConvexFunction_of_convex C h_problem.feasible_convex
  have hindicator_ne_bot :
      ∀ u : E, (δ_ C) u ≠ ⊥ := by
    intro u
    by_cases hu : u ∈ C <;> simp [hu]
  constructor
  · constructor
    · intro u
      by_cases hu : u ∈ C
      · simp [mirrorDescentLinearIndicator, hu]
      · simp [mirrorDescentLinearIndicator, hu]
    · rcases h_problem.feasible_nonempty with ⟨u, huC⟩
      refine ⟨u, ?_⟩
      -- Any feasible point makes the indicator vanish, so the linear term is finite there.
      simp [mirrorDescentLinearIndicator, huC]
  constructor
  · -- Combine convexity of the linear lift with convexity of the feasible-set indicator.
    simpa [mirrorDescentLinearIndicator, Pi.add_apply] using
      is_convex_function_pointwise_add
        hlinearConvexEReal hindicatorConvex hlinear_ne_bot hindicator_ne_bot
  · -- Outside `C` the indicator is `⊤`, and on `C` only the finite linear term remains.
    ext u
    by_cases hu : u ∈ C <;> simp [mirrorDescentLinearIndicator, hu, effective_domain]

/-- Helper for Lemma 9.13: on feasible points, the second-prox objective differs from the mirror
descent update objective only by a constant independent of the comparison point. -/
lemma mirrorDescentSecondProxObjective_eq_update_plusConst_of_mem
    (ω : E → EReal) (C : Set E) (x grad y : E) (step : ℝ) (_hy : y ∈ C) :
    inner ℝ (step • grad) y + B[ω] y x =
      mirror_descent_update_objective (fun z ↦ (ω z).toReal) x grad step y +
        (inner ℝ (∇ (fun z ↦ (ω z).toReal) x) x - (ω x).toReal) := by
  -- Expanding the Bregman term exposes the mirror-descent objective plus the fixed offset.
  rw [mirror_descent_update_objective_apply, bregmanDistance_def]
  rw [inner_sub_right, inner_sub_left]
  ring

/-- Helper for Lemma 9.13: the mirror-descent step minimizer on `C` is also a minimizer of the
second-prox objective on `Set.univ` once the linear-indicator penalty is used. -/
lemma mirrorDescentSecondProxObjective_isMinOnUniv
    (h_traj :
      is_mirror_descent_trajectory (fun y ↦ (f y).toReal) (fun y ↦ (ω y).toReal) C x g t)
    (k : ℕ) :
    IsMinOn (secondProxObjective (mirrorDescentLinearIndicator C (g k) (t k)) ω (x k))
      Set.univ (x (k + 1)) := by
  rw [isMinOn_univ_iff]
  intro y
  rw [SecondProxObjective.apply, SecondProxObjective.apply]
  by_cases hy : y ∈ C
  · -- On feasible points, both objectives differ by the same constant, so the trajectory
    -- minimizer transfers directly.
    let c : ℝ :=
      inner ℝ (∇ (fun z ↦ (ω z).toReal) (x k)) (x k) - (ω (x k)).toReal
    have hxNext : x (k + 1) ∈ C := h_traj.mem_feasible_set (k + 1)
    have hmin :
        mirror_descent_update_objective (fun z ↦ (ω z).toReal) (x k) (g k) (t k) (x (k + 1)) ≤
          mirror_descent_update_objective (fun z ↦ (ω z).toReal) (x k) (g k) (t k) y :=
      (isMinOn_iff.mp (h_traj.isMinOn k)) y hy
    have hxNext_eq :
        mirrorDescentLinearIndicator C (g k) (t k) (x (k + 1)) + B[ω] (x (k + 1)) (x k) =
          (((mirror_descent_update_objective (fun z ↦ (ω z).toReal) (x k) (g k) (t k)
              (x (k + 1)) + c : ℝ)) : EReal) := by
      calc
        mirrorDescentLinearIndicator C (g k) (t k) (x (k + 1)) + B[ω] (x (k + 1)) (x k)
            = ((((inner ℝ (t k • g k) (x (k + 1)) : ℝ)) : EReal) +
                B[ω] (x (k + 1)) (x k)) := by
                  simp [mirrorDescentLinearIndicator, hxNext]
        _ = (((inner ℝ (t k • g k) (x (k + 1)) +
                B[ω] (x (k + 1)) (x k) : ℝ)) : EReal) := by
              rw [← EReal.coe_add]
        _ = (((mirror_descent_update_objective (fun z ↦ (ω z).toReal) (x k) (g k) (t k)
                (x (k + 1)) + c : ℝ)) : EReal) := by
              rw [mirrorDescentSecondProxObjective_eq_update_plusConst_of_mem
                (ω := ω) (C := C) (x := x k) (grad := g k) (y := x (k + 1)) (step := t k) hxNext]
    have hy_eq :
        mirrorDescentLinearIndicator C (g k) (t k) y + B[ω] y (x k) =
          (((mirror_descent_update_objective (fun z ↦ (ω z).toReal) (x k) (g k) (t k) y +
              c : ℝ)) : EReal) := by
      calc
        mirrorDescentLinearIndicator C (g k) (t k) y + B[ω] y (x k)
            = ((((inner ℝ (t k • g k) y : ℝ)) : EReal) + B[ω] y (x k)) := by
                  simp [mirrorDescentLinearIndicator, hy]
        _ = (((inner ℝ (t k • g k) y + B[ω] y (x k) : ℝ)) : EReal) := by
              rw [← EReal.coe_add]
        _ = (((mirror_descent_update_objective (fun z ↦ (ω z).toReal) (x k) (g k) (t k) y +
                c : ℝ)) : EReal) := by
              rw [mirrorDescentSecondProxObjective_eq_update_plusConst_of_mem
                (ω := ω) (C := C) (x := x k) (grad := g k) (y := y) (step := t k) hy]
    have hminE :
        (((mirror_descent_update_objective (fun z ↦ (ω z).toReal) (x k) (g k) (t k)
            (x (k + 1)) + c : ℝ)) : EReal) ≤
          (((mirror_descent_update_objective (fun z ↦ (ω z).toReal) (x k) (g k) (t k) y +
              c : ℝ)) : EReal) := by
      exact EReal.coe_le_coe_iff.mpr (by linarith [hmin])
    calc
      mirrorDescentLinearIndicator C (g k) (t k) (x (k + 1)) + B[ω] (x (k + 1)) (x k)
          = (((mirror_descent_update_objective (fun z ↦ (ω z).toReal) (x k) (g k) (t k)
                (x (k + 1)) + c : ℝ)) : EReal) := hxNext_eq
      _ ≤ (((mirror_descent_update_objective (fun z ↦ (ω z).toReal) (x k) (g k) (t k) y +
                c : ℝ)) : EReal) := hminE
      _ = mirrorDescentLinearIndicator C (g k) (t k) y + B[ω] y (x k) := hy_eq.symm
  · -- Outside `C`, the indicator is `⊤`, so the second-prox objective is automatically larger.
    have hy_top : mirrorDescentLinearIndicator C (g k) (t k) y = ⊤ := by
      simp [mirrorDescentLinearIndicator, hy]
    have hright_top :
        (mirrorDescentLinearIndicator C (g k) (t k) y + B[ω] y (x k) : EReal) = ⊤ := by
      rw [hy_top]
      simpa using EReal.top_add_of_ne_bot (EReal.coe_ne_bot (B[ω] y (x k)))
    calc
      mirrorDescentLinearIndicator C (g k) (t k) (x (k + 1)) + B[ω] (x (k + 1)) (x k) ≤ ⊤ := le_top
      _ = mirrorDescentLinearIndicator C (g k) (t k) y + B[ω] y (x k) := hright_top.symm

/-- Helper for Lemma 9.13: the three-point Bregman identity in add form, written directly in the
normal form consumed by the one-step mirror-descent estimate. -/
lemma mirrorDescentThreePointAddForm
    (ω : E → EReal) (x a u : E) :
    inner ℝ
        ((∇ (fun z ↦ (ω z).toReal) x) - (∇ (fun z ↦ (ω z).toReal) a))
        (u - a) +
      B[ω] u x =
    B[ω] u a + B[ω] a x := by
  -- Route correction: expand the three Bregman terms directly to avoid extra gradient witnesses.
  rw [bregmanDistance_def, bregmanDistance_def, bregmanDistance_def]
  have hsplit : u - x = (u - a) + (a - x) := by
    abel
  rw [hsplit, inner_add_right, inner_sub_left]
  ring

omit [CompleteSpace E] in
/-- Helper for Lemma 9.13: a subgradient of the real-valued lift `x ↦ (ω x).toReal` at a
feasible point is also a subgradient of the owner potential `ω`. -/
lemma mem_subdifferential_of_mem_subdifferential_toReal
    (hω : IsBregmanPotentialOn ω C σ)
    {y : E} (hyC : y ∈ C) {s : Module.Dual ℝ E}
    (hs : s ∈ subdifferential (Function.toEReal (fun z ↦ (ω z).toReal)) y) :
    s ∈ subdifferential ω y := by
  -- Rewrite the lifted certificate into a real inequality, then lift it back through `ω.toReal`.
  have hy : y ∈ effective_domain ω := hω.subset_effective_domain hyC
  change s ∈ subdifferential (fun z ↦ (((ω z).toReal : ℝ) : EReal)) y at hs
  rw [mem_subdifferential, is_subgradient_at_coe_iff] at hs
  rw [mem_subdifferential, is_subgradient_at_iff_forall_mem_effective_domain]
  refine ⟨hy, ?_⟩
  intro z hz
  have hy_top : ω y ≠ ⊤ := ne_of_lt hy
  have hz_top : ω z ≠ ⊤ := ne_of_lt hz
  have hy_bot : ω y ≠ ⊥ := hω.toIsProperExtendedRealFunction.ne_bot y
  have hz_bot : ω z ≠ ⊥ := hω.toIsProperExtendedRealFunction.ne_bot z
  have hsz : (ω z).toReal ≥ (ω y).toReal + s (z - y) := hs z
  have hszE :
      (((ω y).toReal + s (z - y) : ℝ) : EReal) ≤ ((((ω z).toReal : ℝ) : EReal) : EReal) := by
    exact EReal.coe_le_coe (by simpa [ge_iff_le] using hsz)
  simpa [EReal.coe_toReal hy_top hy_bot, EReal.coe_toReal hz_top hz_bot,
    EReal.coe_add, ge_iff_le] using hszE

/-- Helper for Lemma 9.13: the trajectory's domain clause for `ω.toReal` transports to the owner
domain membership `x k ∈ subdifferential_domain ω`. -/
lemma mirrorDescent_memSubdifferentialDomain
    (hω : IsBregmanPotentialOn ω C σ)
    (h_traj :
      is_mirror_descent_trajectory (fun y ↦ (f y).toReal) (fun y ↦ (ω y).toReal) C x g t)
    (k : ℕ) :
    x k ∈ subdifferential_domain ω := by
  -- Extract a lifted subgradient witness and transport it back to the Chapter 9 owner `ω`.
  have hx_domain :
      x k ∈ subdifferential_domain (Function.toEReal (fun y ↦ (ω y).toReal)) :=
    h_traj.mem_subdifferential_domain k
  rw [mem_subdifferential_domain] at hx_domain
  rw [mem_subdifferential_domain]
  rcases hx_domain with ⟨s, hs⟩
  exact ⟨s, mem_subdifferential_of_mem_subdifferential_toReal hω
    (h_traj.mem_feasible_set k) hs⟩

/-- Helper for Lemma 9.13: a differentiable convex objective minimized on a convex set has
nonnegative gradient pairing with every feasible displacement. -/
lemma mirrorDescentGradientNonnegOfIsMinOn
    {F : E → ℝ} {a u grad : E} (hC : Convex ℝ C) (ha : a ∈ C) (hu : u ∈ C)
    (hmin : IsMinOn F C a)
    (hderiv : HasFDerivWithinAt F ((InnerProductSpace.toDual ℝ E) grad) C a) :
    0 ≤ inner ℝ grad (u - a) := by
  -- Route correction: use the tangent-cone first-order optimality API instead of rebuilding the
  -- one-dimensional segment argument by hand.
  have hlocal : IsLocalMinOn F C a := hmin.localize
  have hsegment : segment ℝ a u ⊆ C := hC.segment_subset ha hu
  have hdir : u - a ∈ posTangentConeAt C a :=
    sub_mem_posTangentConeAt_of_segment_subset hsegment
  have hnonneg :
      0 ≤ ((InnerProductSpace.toDual ℝ E) grad) (u - a) :=
    hlocal.hasFDerivWithinAt_nonneg hderiv hdir
  simpa [InnerProductSpace.toDual_apply_apply] using hnonneg

/-- Helper for Lemma 9.13: subtracting two Bregman distances with the same base point collapses
to one potential difference and one gradient pairing. -/
lemma bregmanDifference_sub_sameBase
    (ω : E → EReal) (u y x0 : E) :
    B[ω] u x0 - B[ω] y x0 =
      (ω u).toReal - (ω y).toReal -
        inner ℝ (∇ (fun z ↦ (ω z).toReal) x0) (u - y) := by
  -- Expand both Bregman terms at the common base `x0`; the shared base contribution cancels.
  let grad := ∇ (fun z ↦ (ω z).toReal) x0
  calc
    B[ω] u x0 - B[ω] y x0 =
        (ω u).toReal - (ω y).toReal -
          (inner ℝ grad (u - x0) - inner ℝ grad (y - x0)) := by
      rw [bregmanDistance_def, bregmanDistance_def]
      dsimp [grad]
      ring
    _ =
        (ω u).toReal - (ω y).toReal -
          inner ℝ grad (u - y) := by
      congr 1
      calc
        inner ℝ grad (u - x0) - inner ℝ grad (y - x0)
            = (inner ℝ grad u - inner ℝ grad x0) - (inner ℝ grad y - inner ℝ grad x0) := by
                rw [inner_sub_right, inner_sub_right]
        _ = inner ℝ grad u - inner ℝ grad y := by ring
        _ = inner ℝ grad (u - y) := by
              rw [inner_sub_right]

/-- Helper for Lemma 9.13: adding the mirror-descent linear term preserves the mirror potential's
`σ`-strong convexity on the feasible set. -/
lemma mirrorDescentUpdateObjective_strongConvexOn
    (hω : IsBregmanPotentialOn ω C σ) (k : ℕ) :
    StrongConvexOn C σ
      (mirror_descent_update_objective (fun z ↦ (ω z).toReal) (x k) (g k) (t k)) := by
  -- A linear perturbation does not change the strong-convexity modulus.  Proving this directly
  -- avoids relying on the removed Chapter 5 real-lift helper API.
  refine ⟨hω.strongConvexOn.1, ?_⟩
  intro a ha b hb α β hα hβ hαβ
  have hw := hω.strongConvexOn.2 ha hb hα hβ hαβ
  let v := t k • g k - ∇ (fun z ↦ (ω z).toReal) (x k)
  calc
    mirror_descent_update_objective (fun z ↦ (ω z).toReal) (x k) (g k) (t k)
          (α • a + β • b) =
        (ω (α • a + β • b)).toReal +
          (α * inner ℝ v a + β * inner ℝ v b) := by
            simp [mirror_descent_update_objective_apply, v, inner_add_right,
              inner_smul_right, add_comm]
    _ ≤ (α * (ω a).toReal + β * (ω b).toReal -
          α * β * (σ / 2 * ‖a - b‖ ^ (2 : ℕ))) +
          (α * inner ℝ v a + β * inner ℝ v b) := by
            simpa [smul_eq_mul, add_comm, add_left_comm, add_assoc] using
              (add_le_add_right hw (α * inner ℝ v a + β * inner ℝ v b))
    _ = α • mirror_descent_update_objective (fun z ↦ (ω z).toReal) (x k) (g k) (t k) a +
          β • mirror_descent_update_objective (fun z ↦ (ω z).toReal) (x k) (g k) (t k) b -
          α * β * (σ / 2 * ‖a - b‖ ^ (2 : ℕ)) := by
            simp [mirror_descent_update_objective_apply, v, smul_eq_mul]
            ring

omit [CompleteSpace E] in
/-- Helper for Lemma 9.13: a minimizer of a `σ`-strongly convex function lies at least
`(σ / 2) ‖u - a‖²` below every other feasible point. -/
lemma strongConvexOn_minimizer_quadratic_bound
    {F : E → ℝ} (hF : StrongConvexOn C σ F) (hσ : 0 < σ)
    {a u : E} (ha : a ∈ C) (hu : u ∈ C) (hmin : IsMinOn F C a) :
    F a + (σ / 2) * ‖u - a‖ ^ (2 : ℕ) ≤ F u := by
  by_cases hua : u = a
  · -- On the diagonal the quadratic term vanishes.
    subst hua
    simp
  · set q : ℝ := (σ / 2) * ‖u - a‖ ^ (2 : ℕ)
    have hq_pos : 0 < q := by
      -- Off the diagonal, the quadratic penalty is strictly positive.
      dsimp [q]
      have hnorm_pos : 0 < ‖u - a‖ := by
        refine norm_pos_iff.mpr ?_
        exact sub_ne_zero.mpr hua
      positivity
    by_contra hfail
    have hfail' : F u < F a + q := by
      linarith
    set δ : ℝ := q - (F u - F a)
    have hδ_pos : 0 < δ := by
      dsimp [δ]
      linarith
    set α : ℝ := min (1 / 2 : ℝ) (δ / (2 * q))
    have hα_pos : 0 < α := by
      dsimp [α]
      refine lt_min ?_ ?_
      · norm_num
      · positivity
    have hα_nonneg : 0 ≤ α := hα_pos.le
    have hα_le_half : α ≤ (1 / 2 : ℝ) := by
      dsimp [α]
      exact min_le_left _ _
    have hα_le_one : α ≤ 1 := by
      linarith
    have h_one_sub_nonneg : 0 ≤ 1 - α := by
      linarith
    let z : E := (1 - α) • a + α • u
    have hz : z ∈ C := by
      -- Strong convexity carries convexity of the feasible set.
      exact hF.1 ha hu h_one_sub_nonneg hα_nonneg (by linarith)
    have hmin_le : F a ≤ F z := (isMinOn_iff.mp hmin) z hz
    have hstrong_z :
        F z ≤ (1 - α) * F a + α * F u - (1 - α) * α * q := by
      -- Evaluate strong convexity at the short segment point `z`.
      dsimp [z, q]
      simpa [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm, norm_sub_rev] using
        hF.2 ha hu h_one_sub_nonneg hα_nonneg (by linarith)
    have hαq_le_halfδ : α * q ≤ δ / 2 := by
      -- The choice of `α` makes the residual quadratic term small.
      have hα_le_ratio : α ≤ δ / (2 * q) := by
        dsimp [α]
        exact min_le_right _ _
      have hmul :
          α * q ≤ (δ / (2 * q)) * q := by
        exact mul_le_mul_of_nonneg_right hα_le_ratio hq_pos.le
      calc
        α * q ≤ (δ / (2 * q)) * q := hmul
        _ = δ / 2 := by
          field_simp [hq_pos.ne']
    have hαsq_q_le : α ^ (2 : ℕ) * q ≤ α * (δ / 2) := by
      nlinarith [hαq_le_halfδ, hα_nonneg, hα_le_one]
    have hdrop : α ^ (2 : ℕ) * q < α * δ := by
      nlinarith [hαsq_q_le, hα_pos, hδ_pos]
    have hrewrite :
        (1 - α) * F a + α * F u - (1 - α) * α * q =
          F a - α * δ + α ^ (2 : ℕ) * q := by
      dsimp [δ, q]
      ring
    have hupper_lt :
        (1 - α) * F a + α * F u - (1 - α) * α * q < F a := by
      rw [hrewrite]
      nlinarith [hdrop]
    exact (not_lt_of_ge hmin_le) (lt_of_le_of_lt hstrong_z hupper_lt)

/-- Helper for Lemma 9.13: strong convexity of the update objective yields the same-base forward
comparison with an explicit quadratic penalty at the next iterate. -/
lemma mirrorDescent_stepPairingNext_le_sameBaseDifference_sub_quadratic
    (hω : IsBregmanPotentialOn ω C σ)
    (h_traj :
      is_mirror_descent_trajectory (fun y ↦ (f y).toReal) (fun y ↦ (ω y).toReal) C x g t)
    (k : ℕ) {u : E} (hu : u ∈ C) :
    t k * inner ℝ (g k) (x (k + 1) - u) ≤
      B[ω] u (x k) - B[ω] (x (k + 1)) (x k) -
        (σ / 2) * ‖u - x (k + 1)‖ ^ (2 : ℕ) := by
  have hxNext : x (k + 1) ∈ C := h_traj.mem_feasible_set (k + 1)
  let c : ℝ := inner ℝ (∇ (fun z ↦ (ω z).toReal) (x k)) (x k) - (ω (x k)).toReal
  have hmin :
      mirror_descent_update_objective (fun z ↦ (ω z).toReal) (x k) (g k) (t k) (x (k + 1)) +
          (σ / 2) * ‖u - x (k + 1)‖ ^ (2 : ℕ) ≤
        mirror_descent_update_objective (fun z ↦ (ω z).toReal) (x k) (g k) (t k) u := by
    -- Apply the strong-convex minimizer gap to the trajectory minimizer on the feasible set.
    exact
      strongConvexOn_minimizer_quadratic_bound
        (C := C)
        (σ := σ)
        (F := mirror_descent_update_objective (fun z ↦ (ω z).toReal) (x k) (g k) (t k))
        (mirrorDescentUpdateObjective_strongConvexOn
          (ω := ω) (C := C) (x := x) (g := g) (t := t) hω k)
        hω.sigma_pos hxNext hu (h_traj.isMinOn k)
  have hmin' :
      inner ℝ (t k • g k) (x (k + 1)) + B[ω] (x (k + 1)) (x k) +
          (σ / 2) * ‖u - x (k + 1)‖ ^ (2 : ℕ) ≤
        inner ℝ (t k • g k) u + B[ω] u (x k) := by
    -- Rewrite the strong-convexity comparison into the Bregman-form objective and cancel
    -- the common constant offset.
    have hxNext_eq :
        inner ℝ (t k • g k) (x (k + 1)) + B[ω] (x (k + 1)) (x k) =
          mirror_descent_update_objective (fun z ↦ (ω z).toReal) (x k) (g k) (t k) (x (k + 1)) +
            c :=
      mirrorDescentSecondProxObjective_eq_update_plusConst_of_mem
        (ω := ω) (C := C) (x := x k) (grad := g k) (y := x (k + 1)) (step := t k) hxNext
    have hu_eq :
        inner ℝ (t k • g k) u + B[ω] u (x k) =
          mirror_descent_update_objective (fun z ↦ (ω z).toReal) (x k) (g k) (t k) u + c :=
      mirrorDescentSecondProxObjective_eq_update_plusConst_of_mem
        (ω := ω) (C := C) (x := x k) (grad := g k) (y := u) (step := t k) hu
    calc
      inner ℝ (t k • g k) (x (k + 1)) + B[ω] (x (k + 1)) (x k) +
          (σ / 2) * ‖u - x (k + 1)‖ ^ (2 : ℕ)
          = mirror_descent_update_objective (fun z ↦ (ω z).toReal) (x k) (g k) (t k) (x (k + 1)) +
              c + (σ / 2) * ‖u - x (k + 1)‖ ^ (2 : ℕ) := by
                rw [hxNext_eq]
      _ ≤ mirror_descent_update_objective (fun z ↦ (ω z).toReal) (x k) (g k) (t k) u + c := by
            linarith
      _ = inner ℝ (t k • g k) u + B[ω] u (x k) := by
            rw [hu_eq]
  have hpair :
      t k * inner ℝ (g k) (x (k + 1) - u) =
        inner ℝ (t k • g k) (x (k + 1)) - inner ℝ (t k • g k) u := by
    -- The forward pairing is exactly the difference of the two linearized terms.
    calc
      t k * inner ℝ (g k) (x (k + 1) - u)
          = inner ℝ (t k • g k) (x (k + 1) - u) := by
              simpa using
                (inner_smul_left (g k) (x (k + 1) - u) (t k)).symm
      _ = inner ℝ (t k • g k) (x (k + 1)) - inner ℝ (t k • g k) u := by
            rw [inner_sub_right]
  linarith

/-- Helper for Lemma 9.13: each mirror-descent step satisfies the generic comparison-point
inequality before specializing to an optimizer. -/
lemma mirrorDescent_stepPairingNext_le_sameBaseDifference
    (hω : IsBregmanPotentialOn ω C σ)
    (h_traj :
      is_mirror_descent_trajectory (fun y ↦ (f y).toReal) (fun y ↦ (ω y).toReal) C x g t)
    (k : ℕ) {u : E} (hu : u ∈ C) :
    t k * inner ℝ (g k) (x (k + 1) - u) ≤
      B[ω] u (x k) - B[ω] (x (k + 1)) (x k) := by
  -- Route correction: first prove the stronger quadratic comparison, then drop the nonnegative
  -- penalty term to recover the textbook same-base bound.
  have hquadratic :
      t k * inner ℝ (g k) (x (k + 1) - u) ≤
        B[ω] u (x k) - B[ω] (x (k + 1)) (x k) -
          (σ / 2) * ‖u - x (k + 1)‖ ^ (2 : ℕ) :=
    mirrorDescent_stepPairingNext_le_sameBaseDifference_sub_quadratic
      (f := f) (ω := ω) (C := C) (σ := σ) (x := x) (g := g) (t := t) hω h_traj k hu
  have hpenalty_nonneg : 0 ≤ (σ / 2) * ‖u - x (k + 1)‖ ^ (2 : ℕ) := by
    -- Strong convexity makes the quadratic penalty nonnegative, so removing it weakens the bound.
    have hnorm_sq_nonneg : 0 ≤ ‖u - x (k + 1)‖ ^ (2 : ℕ) := by positivity
    nlinarith [hω.sigma_pos, hnorm_sq_nonneg]
  linarith

/-- Helper for Lemma 9.13: the mixed step-displacement pairing is absorbed by the one-step
Bregman term and the standard Young correction. -/
lemma mirrorDescent_stepDisplacement_le_bregmanCorrection
    (hω : IsBregmanPotentialOn ω C σ)
    (hω_diff : ∀ z ∈ subdifferential_domain ω,
      DifferentiableAt ℝ (fun w ↦ (ω w).toReal) z)
    (h_traj :
      is_mirror_descent_trajectory (fun y ↦ (f y).toReal) (fun y ↦ (ω y).toReal) C x g t)
    (k : ℕ) :
    t k * inner ℝ (g k) (x k - x (k + 1)) ≤
      B[ω] (x (k + 1)) (x k) +
        (t k) ^ (2 : ℕ) * ‖g k‖ ^ (2 : ℕ) / (2 * σ) := by
  have hxk : x k ∈ C := h_traj.mem_feasible_set k
  have hxNext : x (k + 1) ∈ C := h_traj.mem_feasible_set (k + 1)
  have hxk_sub : x k ∈ subdifferential_domain ω :=
    mirrorDescent_memSubdifferentialDomain hω h_traj k
  have hB :
      (σ / 2) * ‖x (k + 1) - x k‖ ^ (2 : ℕ) ≤ B[ω] (x (k + 1)) (x k) := by
    -- The Chapter 9 lower quadratic bound controls the one-step Bregman term from below.
    exact bregmanDistance_lower_quadratic_bound hω (x (k + 1)) (x k) hxNext hxk hxk_sub
      (hω_diff (x k) hxk_sub)
  have hpair :
      t k * inner ℝ (g k) (x k - x (k + 1)) ≤
        t k * ‖g k‖ * ‖x k - x (k + 1)‖ := by
    -- First dominate the inner product by the product of norms.
    have hinner : inner ℝ (g k) (x k - x (k + 1)) ≤ ‖g k‖ * ‖x k - x (k + 1)‖ :=
      real_inner_le_norm _ _
    have hstep_nonneg : 0 ≤ t k := le_of_lt (h_traj.stepsize_pos k)
    nlinarith
  have hyoung :
      t k * ‖g k‖ * ‖x k - x (k + 1)‖ ≤
        (σ / 2) * ‖x (k + 1) - x k‖ ^ (2 : ℕ) +
          (t k) ^ (2 : ℕ) * ‖g k‖ ^ (2 : ℕ) / (2 * σ) := by
    -- Apply Young's inequality after normalizing the displacement norm to the Bregman surface.
    have hnorm_rev : ‖x k - x (k + 1)‖ = ‖x (k + 1) - x k‖ := norm_sub_rev _ _
    have hyoung_aux :
        2 * ‖x (k + 1) - x k‖ * (t k * ‖g k‖) ≤
          σ * ‖x (k + 1) - x k‖ ^ (2 : ℕ) + σ⁻¹ * (t k * ‖g k‖) ^ (2 : ℕ) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        two_mul_le_add_mul_sq (a := ‖x (k + 1) - x k‖) (b := t k * ‖g k‖) hω.sigma_pos
    have hdouble :
        2 * (t k * ‖g k‖ * ‖x k - x (k + 1)‖) ≤
          2 * ((σ / 2) * ‖x (k + 1) - x k‖ ^ (2 : ℕ) +
            (t k) ^ (2 : ℕ) * ‖g k‖ ^ (2 : ℕ) / (2 * σ)) := by
      calc
        2 * (t k * ‖g k‖ * ‖x k - x (k + 1)‖)
            = 2 * ‖x (k + 1) - x k‖ * (t k * ‖g k‖) := by
                rw [hnorm_rev]
                ring
        _ ≤ σ * ‖x (k + 1) - x k‖ ^ (2 : ℕ) + σ⁻¹ * (t k * ‖g k‖) ^ (2 : ℕ) := hyoung_aux
        _ =
            2 * ((σ / 2) * ‖x (k + 1) - x k‖ ^ (2 : ℕ) +
              (t k) ^ (2 : ℕ) * ‖g k‖ ^ (2 : ℕ) / (2 * σ)) := by
                field_simp [pow_two, hω.sigma_pos.ne']
    nlinarith
  linarith

/-- Helper for Lemma 9.13: the textbook three-point Bregman drop is exactly the negative
gradient-gap pairing from the add-form three-point identity. -/
lemma mirrorDescent_targetDrop_eq_neg_threePointPairing
    (ω : E → EReal) (x a u : E) :
    B[ω] u x - B[ω] u a - B[ω] a x =
      -inner ℝ
        ((∇ (fun z ↦ (ω z).toReal) x) - (∇ (fun z ↦ (ω z).toReal) a))
        (u - a) := by
  -- Repackage the add-form three-point identity into the exact subtraction surface used below.
  have hadd :
      inner ℝ
          ((∇ (fun z ↦ (ω z).toReal) x) - (∇ (fun z ↦ (ω z).toReal) a))
          (u - a) +
        B[ω] u x =
      B[ω] u a + B[ω] a x :=
    mirrorDescentThreePointAddForm ω x a u
  linarith

/-- Helper for Lemma 9.13: first-order optimality of the mirror-descent update objective yields
the exact one-step variational inequality at the next iterate. -/
lemma mirrorDescentStepVariationalIneq
    (h_problem : IsConstrainedConvexProblem f C XStar fOpt)
    (hω : IsBregmanPotentialOn ω C σ)
    (hω_diff : ∀ z ∈ subdifferential_domain ω,
      DifferentiableAt ℝ (fun w ↦ (ω w).toReal) z)
    (h_traj :
      is_mirror_descent_trajectory (fun y ↦ (f y).toReal) (fun y ↦ (ω y).toReal) C x g t)
    (k : ℕ) {u : E} (hu : u ∈ C) :
    inner ℝ
        ((∇ (fun z ↦ (ω z).toReal) (x k)) - (∇ (fun z ↦ (ω z).toReal) (x (k + 1))))
        (u - x (k + 1)) ≤
      t k * inner ℝ (g k) (u - x (k + 1)) := by
  let a := x (k + 1)
  have ha : a ∈ C := h_traj.mem_feasible_set (k + 1)
  have haω : a ∈ subdifferential_domain ω := by
    simpa [a] using mirrorDescent_memSubdifferentialDomain hω h_traj (k + 1)
  let v : E := t k • g k - ∇ (fun z ↦ (ω z).toReal) (x k)
  have hlinear : HasFDerivAt (fun z : E ↦ inner ℝ v z)
      (InnerProductSpace.toDual ℝ E v) a :=
    (InnerProductSpace.toDual ℝ E v).hasFDerivAt
  have hpotential : HasFDerivAt (fun z ↦ (ω z).toReal)
      (InnerProductSpace.toDual ℝ E (∇ (fun z ↦ (ω z).toReal) a)) a :=
    (hω_diff a haω).hasGradientAt.hasFDerivAt
  have hupdate : HasFDerivWithinAt
      (mirror_descent_update_objective (fun z ↦ (ω z).toReal) (x k) (g k) (t k))
      (InnerProductSpace.toDual ℝ E
        (v + ∇ (fun z ↦ (ω z).toReal) a)) C a := by
    have hadd := (hlinear.add hpotential).hasFDerivWithinAt (s := C)
    simpa [mirror_descent_update_objective_apply, v, map_add] using hadd
  have hnonneg :
      0 ≤ inner ℝ (v + ∇ (fun z ↦ (ω z).toReal) a) (u - a) :=
    mirrorDescentGradientNonnegOfIsMinOn
      (C := C) h_problem.feasible_convex ha hu (h_traj.isMinOn k) hupdate
  dsimp [v, a] at hnonneg ⊢
  rw [inner_add_left, inner_sub_left, real_inner_smul_left] at hnonneg
  rw [inner_sub_left]
  linarith

/-- Helper for Lemma 9.13: the exact forward three-point comparison is the only remaining gap
after the strong-convexity reduction. -/
lemma mirrorDescent_stepPairingNext_le_threePointDifference
    (h_problem : IsConstrainedConvexProblem f C XStar fOpt)
    (hω : IsBregmanPotentialOn ω C σ)
    (hω_diff : ∀ z ∈ subdifferential_domain ω,
      DifferentiableAt ℝ (fun w ↦ (ω w).toReal) z)
    (h_traj :
      is_mirror_descent_trajectory (fun y ↦ (f y).toReal) (fun y ↦ (ω y).toReal) C x g t)
    (k : ℕ) {u : E} (hu : u ∈ C) :
    t k * inner ℝ (g k) (x (k + 1) - u) ≤
      B[ω] u (x k) - B[ω] u (x (k + 1)) - B[ω] (x (k + 1)) (x k) := by
  have hvariational :
      inner ℝ
          ((∇ (fun z ↦ (ω z).toReal) (x k)) - (∇ (fun z ↦ (ω z).toReal) (x (k + 1))))
          (u - x (k + 1)) ≤
        t k * inner ℝ (g k) (u - x (k + 1)) :=
    mirrorDescentStepVariationalIneq
      (f := f) (ω := ω) (C := C) (XStar := XStar) (fOpt := fOpt)
      (σ := σ) (x := x) (g := g) (t := t) h_problem hω hω_diff h_traj k hu
  have hsplit :
      t k * inner ℝ (g k) (x (k + 1) - u) =
        -(t k * inner ℝ (g k) (u - x (k + 1))) := by
    -- Rewrite the forward displacement by reversing the comparison vector.
    rw [show x (k + 1) - u = -(u - x (k + 1)) by abel, inner_neg_right]
    ring
  -- Route correction: use the exact step variational inequality, then rewrite the target drop
  -- with the three-point identity instead of weakening it to a quadratic bound.
  rw [hsplit, mirrorDescent_targetDrop_eq_neg_threePointPairing]
  nlinarith

lemma mirrorDescent_stepPairing_le_bregmanDrop
    (h_problem : IsConstrainedConvexProblem f C XStar fOpt)
    (hω : IsBregmanPotentialOn ω C σ)
    (hω_diff : ∀ z ∈ subdifferential_domain ω,
      DifferentiableAt ℝ (fun w ↦ (ω w).toReal) z)
    (h_traj :
      is_mirror_descent_trajectory (fun y ↦ (f y).toReal) (fun y ↦ (ω y).toReal) C x g t)
    (k : ℕ) {u : E} (hu : u ∈ C) :
    t k * inner ℝ (g k) (x k - u) ≤
      B[ω] u (x k) - B[ω] u (x (k + 1)) +
        (t k) ^ (2 : ℕ) * ‖g k‖ ^ (2 : ℕ) / (2 * σ) := by
  let _ := h_problem
  have hforward :
      t k * inner ℝ (g k) (x (k + 1) - u) ≤
        B[ω] u (x k) - B[ω] u (x (k + 1)) - B[ω] (x (k + 1)) (x k) :=
    mirrorDescent_stepPairingNext_le_threePointDifference
      (f := f) (ω := ω) (C := C) (XStar := XStar) (fOpt := fOpt)
      (σ := σ) (x := x) (g := g) (t := t) h_problem hω hω_diff h_traj k hu
  have hdisplacement :
      t k * inner ℝ (g k) (x k - x (k + 1)) ≤
        B[ω] (x (k + 1)) (x k) +
          (t k) ^ (2 : ℕ) * ‖g k‖ ^ (2 : ℕ) / (2 * σ) :=
    mirrorDescent_stepDisplacement_le_bregmanCorrection
      (f := f) (ω := ω) (C := C) (σ := σ) (x := x) (g := g) (t := t)
      hω hω_diff h_traj k
  have hsplit :
      t k * inner ℝ (g k) (x k - u) =
        t k * inner ℝ (g k) (x (k + 1) - u) +
          t k * inner ℝ (g k) (x k - x (k + 1)) := by
    -- Split the step pairing into the forward comparison term and the displacement term.
    have hdecomp : x k - u = (x (k + 1) - u) + (x k - x (k + 1)) := by
      abel
    rw [hdecomp, inner_add_right]
    ring
  -- The exact forward three-point drop and the displacement correction now assemble directly.
  rw [hsplit]
  linarith

/-- Helper for Lemma 9.13: the chosen mirror-descent subgradient controls the optimality gap by
the usual subgradient inequality at the current iterate. -/
lemma mirrorDescent_subgradientGap_le_pairing
    (h_problem : IsConstrainedConvexProblem f C XStar fOpt)
    (h_traj :
      is_mirror_descent_trajectory (fun y ↦ (f y).toReal) (fun y ↦ (ω y).toReal) C x g t)
    {xStar : E} (hxStar : xStar ∈ XStar) (k : ℕ) :
    (f (x k)).toReal - fOpt ≤ inner ℝ (g k) (x k - xStar) := by
  have hsub :=
    h_traj.subgradient_mem k
  rw [mem_euclideanSubdifferentialAt_iff, subdifferentialAt, mem_strongDualSubdifferential,
    mem_subdifferential, is_subgradient_at_coe_iff] at hsub
  have hpointwise :
      (f xStar).toReal ≥ (f (x k)).toReal + inner ℝ (g k) (xStar - x k) :=
    hsub xStar
  have hreverse :
      inner ℝ (g k) (xStar - x k) = -inner ℝ (g k) (x k - xStar) := by
    rw [show xStar - x k = -(x k - xStar) by abel, inner_neg_right]
  -- Substitute the optimal-point value and reorient the displacement toward `xStar`.
  rw [optimal_point_toReal_eq_fOpt h_problem hxStar] at hpointwise
  nlinarith [hpointwise, hreverse]

/-- Lemma 9.13: under the standing constrained-problem assumptions of Definition 9.1 and the
Bregman-potential assumptions of Definition 9.2, every step of a mirror-descent trajectory
satisfies the fundamental inequality
`t_k (f(x^k).toReal - f_opt) ≤ B_ω(xStar, x^k) - B_ω(xStar, x^(k+1)) + t_k^2 ‖g_k‖^2 / (2σ)` for
each optimal point `xStar ∈ XStar`. -/
theorem mirror_descent_fundamental_inequality
    (h_problem : IsConstrainedConvexProblem f C XStar fOpt)
    (hω : IsBregmanPotentialOn ω C σ)
    (hω_diff : ∀ z ∈ subdifferential_domain ω,
      DifferentiableAt ℝ (fun w ↦ (ω w).toReal) z)
    (h_traj :
      is_mirror_descent_trajectory (fun y ↦ (f y).toReal) (fun y ↦ (ω y).toReal) C x g t)
    {xStar : E} (hxStar : xStar ∈ XStar) (k : ℕ) :
    t k * ((f (x k)).toReal - fOpt) ≤
      B[ω] xStar (x k) - B[ω] xStar (x (k + 1)) +
        (t k) ^ (2 : ℕ) * ‖g k‖ ^ (2 : ℕ) / (2 * σ) := by
  have hxStar_data : xStar ∈ C ∧ IsMinOn f C xStar := by
    simpa [h_problem.optimal_set_eq] using hxStar
  have hgap :
      (f (x k)).toReal - fOpt ≤ inner ℝ (g k) (x k - xStar) :=
    mirrorDescent_subgradientGap_le_pairing
      (f := f) (ω := ω) (C := C) (XStar := XStar) (fOpt := fOpt)
      (x := x) (g := g) (t := t) h_problem h_traj hxStar k
  have hstep :
      t k * inner ℝ (g k) (x k - xStar) ≤
        B[ω] xStar (x k) - B[ω] xStar (x (k + 1)) +
          (t k) ^ (2 : ℕ) * ‖g k‖ ^ (2 : ℕ) / (2 * σ) :=
    mirrorDescent_stepPairing_le_bregmanDrop
      (f := f) (ω := ω) (C := C) (XStar := XStar) (fOpt := fOpt)
      (σ := σ) (x := x) (g := g) (t := t) h_problem hω hω_diff h_traj k hxStar_data.1
  -- Multiply the subgradient-gap inequality by the positive stepsize and then plug it into the
  -- generic one-step comparison inequality.
  nlinarith [h_traj.stepsize_pos k, hgap, hstep]

end

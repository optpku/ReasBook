/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap08.Algorithm_8_3
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Assumption_8_7
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Assumption_8_12
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_8
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Lemma_8_24
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Proposition_5_13
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Theorem_5_26
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Definition_9_2
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Definition_9_3
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Text_9_5
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Theorem_9_16

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open InnerProductSpace (toDualMap)
open WithLp (toLp)

noncomputable section

section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Δ" => (toLp 2 '' (stdSimplex ℝ (Fin n) : Set (Fin n → ℝ)) : Set E)
local notation "ω" => ((fun z : E ↦ ‖z‖ ^ (2 : ℕ) / 2) : E → ℝ)
local notation "ωₑ" => Function.toEReal ω

/- Text 9.8 is `source-facing`: the textbook specializes mirror descent on the simplex to the
Euclidean distance-generating function `ω(x) = ‖x‖₂² / 2`, initialized at the uniform point
`(1 / n) e`. The `core/canonical` owner for this rate statement is therefore the Chapter 9
trajectory predicate `is_mirror_descent_trajectory` together with the fixed-horizon rate theorem
`mirror_descent_best_value_gap_le_one_div_sqrt_of_constant_stepsizes`; the Euclidean
projected-subgradient formulation is only a `bridge/view`, supplied by Text 9.5. In the current
project the ambient Euclidean owner is `EuclideanSpace ℝ (Fin n)`, the simplex is the transported
set `toLp 2 '' stdSimplex ℝ (Fin n)`, and the uniform initial point is the transport of the
canonical simplex barycenter. -/

-- The coordinate-side owner is `stdSimplex.barycenter`; `uniform_simplex_point` is only its
-- Euclidean transported view in the image simplex `Δ`.
/-- The canonical uniform initial point `x⁰ = (1 / n) e` in the Euclidean simplex
`toLp 2 '' stdSimplex ℝ (Fin n)`, obtained by transporting `stdSimplex.barycenter`, for
`n > 0`. -/
abbrev uniform_simplex_point (hn : 0 < n) : Δ :=
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  ⟨toLp 2 (stdSimplex.barycenter : stdSimplex ℝ (Fin n)),
    ⟨stdSimplex.barycenter, stdSimplex.barycenter.2, rfl⟩⟩

-- Proof sketch: `stdSimplex.barycenter` has every coordinate equal to `(Fintype.card (Fin n))⁻¹`,
-- i.e. `1 / n`, and `uniform_simplex_point` is exactly its `toLp 2` transport into the ambient
-- Euclidean space.
/-- Coercing the uniform simplex point to the ambient Euclidean space gives the transported
constant vector with coordinates `1 / n`. -/
@[simp] theorem coe_uniform_simplex_point (hn : 0 < n) :
    (uniform_simplex_point hn : E) = toLp 2 (fun _ : Fin n ↦ 1 / (n : ℝ)) := by
  -- Unfold the transported barycenter and identify each simplex coordinate with `1 / n`.
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  ext i
  have hbary :
      ((stdSimplex.barycenter : stdSimplex ℝ (Fin n)) : Fin n → ℝ) i = (↑n : ℝ)⁻¹ := by
    simpa only [Fintype.card_fin] using
      (stdSimplex.barycenter_apply (𝕜 := ℝ) (X := Fin n) i)
  simpa [uniform_simplex_point] using hbary

/-- Helper for Text 9.8: for `ω(x) = ‖x‖² / 2`, the Bregman distance is
`‖x - y‖² / 2`. -/
lemma bregmanDistance_halfSquaredNorm_eq_half_norm_sub_sq (x y : E) :
    B[ωₑ] x y = ‖x - y‖ ^ (2 : ℕ) / 2 := by
  -- Expand the quadratic Bregman distance and collapse the cross-term with `norm_sub_sq_real`.
  rw [bregmanDistance_apply_real, gradient_half_squared_norm_div_two, inner_sub_right,
    real_inner_self_eq_norm_sq, real_inner_comm]
  nlinarith [norm_sub_sq_real x y]

/-- Helper for Text 9.8: two transported simplex points are at squared Euclidean distance at most
`2`. -/
lemma norm_sq_sub_le_two_of_mem_simplex {x y : E} (hx : x ∈ Δ) (hy : y ∈ Δ) :
    ‖x - y‖ ^ (2 : ℕ) ≤ 2 := by
  rcases hx with ⟨x', hx', rfl⟩
  rcases hy with ⟨y', hy', rfl⟩
  -- Rewrite the Euclidean norm in coordinates and compare each coordinate square by `a² ≤ a`.
  calc
    ‖toLp 2 x' - toLp 2 y'‖ ^ (2 : ℕ) = ∑ i, (x' i - y' i) ^ (2 : ℕ) := by
      simpa using (EuclideanSpace.real_norm_sq_eq (toLp 2 (x' - y')))
    _ ≤ ∑ i, (x' i + y' i) := by
      refine Finset.sum_le_sum ?_
      intro i hi
      have hx0 : 0 ≤ x' i := hx'.1 i
      have hy0 : 0 ≤ y' i := hy'.1 i
      have hx1 : x' i ≤ 1 := (mem_Icc_of_mem_stdSimplex hx' i).2
      have hy1 : y' i ≤ 1 := (mem_Icc_of_mem_stdSimplex hy' i).2
      nlinarith
    _ = 2 := by
      rw [Finset.sum_add_distrib, hx'.2, hy'.2]
      norm_num

/-- Helper for Text 9.8: the quadratic mirror map is subdifferentiable everywhere. -/
lemma mem_subdifferential_domain_halfSquaredNorm (z : E) :
    z ∈ subdifferential_domain ωₑ := by
  have hconvex_real : ConvexOn ℝ Set.univ ω := by
    exact
      ((half_squared_norm_is_one_strongly_convex_on (C := Set.univ) convex_univ).strictConvexOn
        (by norm_num)).convexOn
  have hsub :
      fderiv ℝ ω z ∈ subdifferentialAt ω z := by
    -- The quadratic is convex and differentiable, so its Fréchet derivative is a subgradient.
    exact
      fderiv_mem_subdifferentialAt_of_convexOn_univ hconvex_real
        (hasGradientAt_half_squared_norm_div_two z).differentiableAt
  rw [mem_subdifferential_domain]
  exact ⟨fderiv ℝ ω z, by simpa [subdifferentialAt, Function.toEReal] using hsub⟩

/-- The Euclidean mirror map `ω(x) = ‖x‖² / 2` is a Bregman potential with modulus `1` on the
transported simplex `Δ`. -/
instance half_squared_norm_isBregmanPotentialOn_simplex :
    IsBregmanPotentialOn ωₑ Δ 1 := by
  -- Package the Euclidean quadratic with the canonical Chapter 9 Bregman-potential fields.
  refine
    { toIsProperExtendedRealFunction := Function.toEReal_isProper ω
      closed := ?_
      convex := ?_
      differentiableOn_subdifferential_domain := ?_
      subset_effective_domain := ?_
      sigma_pos := by norm_num
      strongConvexOn := ?_ }
  · -- The quadratic mirror map is continuous, hence lower semicontinuous after coercion to `EReal`.
    exact Function.toEReal_lowerSemicontinuous_of_continuous (by continuity : Continuous ω)
  · have hconvex_real : ConvexOn ℝ Set.univ ω := by
      exact
        ((half_squared_norm_is_one_strongly_convex_on (C := Set.univ) convex_univ).strictConvexOn
          (by norm_num)).convexOn
    exact Function.toEReal_isConvexFunction hconvex_real
  · -- The quadratic is differentiable everywhere, so in particular on `dom(∂ ω)`.
    intro x hx
    exact (hasGradientAt_half_squared_norm_div_two x).differentiableAt.differentiableWithinAt
  · -- A real-valued mirror map is finite everywhere.
    intro x hx
    simp [effective_domain, Function.toEReal]
  · have hΔ_convex : Convex ℝ (Δ : Set E) := by
      change Convex ℝ
        (((WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm.toLinearMap) ''
          (stdSimplex ℝ (Fin n) : Set (Fin n → ℝ)))
      exact
        (convex_stdSimplex ℝ (Fin n)).linear_image
          ((WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm.toLinearMap)
    exact half_squared_norm_is_one_strongly_convex_on (C := Δ) hΔ_convex

-- Proof sketch: for the Euclidean mirror map, the Bregman distance is
-- `(1 / 2) ‖x - x₀‖²`. Two points of the simplex lie in the unit `ℓ₂` ball and differ by at most
-- `√2`, so the resulting Bregman diameter from the uniform initialization is at most `1`.
/-- On the simplex, the Euclidean Bregman distance to the uniform initialization `x⁰ = (1 / n)e`
is bounded by `1`. This is the simplex specialization of the textbook constant `Θ₀ = 1`. -/
theorem half_squared_norm_bregman_le_one_of_mem_simplex
    (hn : 0 < n) {x : E} (hx : x ∈ Δ) :
    B[ωₑ] x (uniform_simplex_point hn) ≤ 1 := by
  -- Normalize the Bregman term to a squared Euclidean distance and apply the simplex diameter bound.
  calc
    B[ωₑ] x (uniform_simplex_point hn)
        = ‖x - uniform_simplex_point hn‖ ^ (2 : ℕ) / 2 := by
            exact bregmanDistance_halfSquaredNorm_eq_half_norm_sub_sq x (uniform_simplex_point hn)
    _ ≤ 2 / 2 := by
          gcongr
          exact norm_sq_sub_le_two_of_mem_simplex hx (uniform_simplex_point hn).property
    _ = 1 := by norm_num

section Rate

variable {f : EuclideanSpace ℝ (Fin n) → EReal}
variable {XStar : Set (EuclideanSpace ℝ (Fin n))} {fOpt : ℝ}
variable (h_problem : IsConstrainedConvexProblem f Δ XStar fOpt)
variable
  (h_bound :
    SubgradientNormBoundOn f
      (toLp 2 '' (stdSimplex ℝ (Fin n) : Set (Fin n → ℝ)) :
        Set (EuclideanSpace ℝ (Fin n))))

-- Proof sketch: apply Theorem 9.16 to the Euclidean mirror map `ω(x) = ‖x‖² / 2` on the simplex
-- `Δ`, use `half_squared_norm_isBregmanPotentialOn_simplex` for the Bregman-potential owner, and
-- bound the initial Bregman term by `1` via
-- `half_squared_norm_bregman_le_one_of_mem_simplex` at the optimal point `xStar ∈ XStar ⊆ Δ`.
-- With `σ = 1`, `Θ₀ = 1`, and the constant stepsize
-- `t_k = √2 / (L_{f,2} √(N + 1))`, Theorem 9.16 reduces exactly to the displayed estimate.
/-- Text 9.8: for mirror descent on the Euclidean simplex with mirror map
`ω(x) = ‖x‖₂² / 2`, uniform initialization `x⁰ = (1 / n)e`, and constant stepsizes
`t_k = √2 / (L_{f,2} √(N + 1))` on the first `N + 1` iterations, the running-best objective gap
is bounded by `√2 L_{f,2} / √(N + 1)`, with `L_{f,2}` represented here by `h_bound.L_f`. -/
theorem euclidean_simplex_mirror_descent_best_value_gap_le
    (hn : 0 < n)
    {x g : ℕ → EuclideanSpace ℝ (Fin n)} {t : ℕ → ℝ}
    (h_problem : IsConstrainedConvexProblem f Δ XStar fOpt)
    (h_traj : is_mirror_descent_trajectory (fun y ↦ (f y).toReal) ω Δ x g t)
    {xStar : EuclideanSpace ℝ (Fin n)} (hxStar : xStar ∈ XStar)
    (hx0 : x 0 = (uniform_simplex_point hn : EuclideanSpace ℝ (Fin n)))
    {N : ℕ}
    (h_stepsize :
      ∀ k : Fin (N + 1),
        t k = Real.sqrt 2 / (h_bound.L_f * Real.sqrt (N + 1 : ℝ))) :
    best_achieved_function_value (fun y ↦ (f y).toReal) x N - fOpt ≤
      Real.sqrt 2 * h_bound.L_f / Real.sqrt (N + 1 : ℝ) := by
  have hω_diff : ∀ z ∈ subdifferential_domain ωₑ,
      DifferentiableAt ℝ (fun w ↦ (ωₑ w).toReal) z := by
    intro z hz
    simpa [Function.toEReal] using
      (hasGradientAt_half_squared_norm_div_two z).differentiableAt
  have h_bregman_upper : B[ωₑ] xStar (x 0) ≤ 1 := by
    rw [hx0]
    apply half_squared_norm_bregman_le_one_of_mem_simplex hn
    exact (by simpa [h_problem.optimal_set_eq] using hxStar : xStar ∈ Δ ∧ IsMinOn f Δ xStar).1
  have h_stepsize' :
      (fun k : Fin (N + 1) ↦ t k) =
        mirror_descent_textbook_stepsize 1 h_bound.L_f 1 N := by
    funext k
    simpa using h_stepsize k
  have h_rate :=
    mirror_descent_best_value_gap_le_one_div_sqrt_of_constant_stepsizes
      h_problem (half_squared_norm_isBregmanPotentialOn_simplex (n := n)) hω_diff h_bound
      h_traj 1 hxStar h_bregman_upper h_stepsize'
  simpa [mul_comm] using h_rate

section Bridge

variable (hn : 0 < n)
variable
  (g : ℕ →
    (toLp 2 '' (stdSimplex ℝ (Fin n) : Set (Fin n → ℝ)) :
      Set (EuclideanSpace ℝ (Fin n))) →
    EuclideanSpace ℝ (Fin n))
  (t : ℕ → ℝ)

local notation "x[" k "]" =>
  projected_subgradient_method Δ h_problem.feasible_nonempty h_problem.feasible_closed
    h_problem.feasible_convex g t (uniform_simplex_point hn) k
local notation "x̄" =>
  projected_subgradient_method_iterate Δ h_problem.feasible_nonempty h_problem.feasible_closed
    h_problem.feasible_convex g t (uniform_simplex_point hn)
local notation "x̄[" k "]" => x̄ k

-- Proof sketch: feasibility of each iterate is automatic because `projected_subgradient_method`
-- is `Δ`-valued, the Euclidean subgradient hypothesis supplies the corresponding trajectory
-- clause, `h_stepsize_pos` supplies positivity, and Text 9.5
-- identifies the projected-subgradient minimization with the Euclidean mirror-descent one-step
-- minimization.
/-- The projected-subgradient iterates on the Euclidean simplex, started at the uniform point,
form the specialized mirror-descent trajectory for `ω(x) = ‖x‖₂² / 2`. This is the explicit
Text 9.5 bridge between the Chapter 8 recursive iterates and the Chapter 9 owner
`is_mirror_descent_trajectory`. -/
theorem projected_subgradient_method_is_mirror_descent_trajectory
    (hn : 0 < n)
    (h_problem : IsConstrainedConvexProblem f Δ XStar fOpt)
    (h_subgrad :
      ∀ k,
        g k
            (projected_subgradient_method Δ h_problem.feasible_nonempty
              h_problem.feasible_closed h_problem.feasible_convex g t
              (uniform_simplex_point (n := n) hn) k) ∈
          euclideanSubdifferentialAt (fun y ↦ (f y).toReal)
            (projected_subgradient_method_iterate Δ h_problem.feasible_nonempty
              h_problem.feasible_closed h_problem.feasible_convex g t
              (uniform_simplex_point (n := n) hn) k))
    (h_stepsize_pos : ∀ k, 0 < t k) :
    is_mirror_descent_trajectory
      (fun y ↦ (f y).toReal)
      ω
      Δ
      (projected_subgradient_method_iterate Δ h_problem.feasible_nonempty
        h_problem.feasible_closed h_problem.feasible_convex g t
        (uniform_simplex_point (n := n) hn))
      (fun k ↦
        g k
          (projected_subgradient_method Δ h_problem.feasible_nonempty h_problem.feasible_closed
            h_problem.feasible_convex g t (uniform_simplex_point (n := n) hn) k))
      t := by
  unfold is_mirror_descent_trajectory
  let x0 : Δ := uniform_simplex_point (n := n) hn
  let xSeq : ℕ → Δ :=
    projected_subgradient_method Δ h_problem.feasible_nonempty h_problem.feasible_closed
      h_problem.feasible_convex g t x0
  let xBar : ℕ → E :=
    projected_subgradient_method_iterate Δ h_problem.feasible_nonempty h_problem.feasible_closed
      h_problem.feasible_convex g t x0
  intro k
  have hxk_mem : xBar k ∈ Δ := by
    -- Every projected-subgradient iterate is simplex-valued by construction.
    simp [xBar, projected_subgradient_method_iterate]
  have hxkp1_mem : xBar (k + 1) ∈ Δ := by
    -- The next iterate is again simplex-valued for the same subtype reason.
    simp [xBar, projected_subgradient_method_iterate]
  have hgk_mem :
      g k (xSeq k) ∈ euclideanSubdifferentialAt (fun y ↦ (f y).toReal) (xBar k) := by
    simpa [xSeq, xBar] using h_subgrad k
  have hstep_eq :
      xBar (k + 1) =
        Pp[Δ, h_problem.feasible_nonempty, h_problem.feasible_closed, h_problem.feasible_convex]
          (xBar k - t k • g k (xSeq k)) := by
    -- The Chapter 8 recursive update is exactly the projection formula used by Text 9.5.
    simpa [xBar, xSeq, projected_subgradient_method_iterate, projectionPoint] using
      projected_subgradient_method_iterate_succ Δ h_problem.feasible_nonempty
        h_problem.feasible_closed h_problem.feasible_convex g t x0 k
  -- Text 9.5 turns the projection update into the Euclidean mirror-descent minimizer condition.
  exact
    ⟨⟨hxk_mem, mem_subdifferential_domain_halfSquaredNorm (xBar k)⟩, hgk_mem,
      h_stepsize_pos k,
      (mirror_descent_half_squared_norm_step_iff_eq_projection
        Δ h_problem.feasible_nonempty h_problem.feasible_closed h_problem.feasible_convex
        (xBar k) (g k (xSeq k)) (xBar (k + 1)) (t k) hxkp1_mem).2 hstep_eq⟩

end Bridge

end Rate

end

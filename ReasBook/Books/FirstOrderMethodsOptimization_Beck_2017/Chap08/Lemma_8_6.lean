/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap08.Algorithm_8_1
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_4
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Lemma_8_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped Gradient

noncomputable section

section

-- Proof sketch: unfold `wolfe_example_function`; the result is exactly the defining piecewise
-- formula from equation (8.5).
/-- Unfolding `wolfe_example_function` gives the two branches from Wolfe's example. -/
@[simp] theorem wolfe_example_function_apply (γ : ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    wolfe_example_function γ x =
      if |x 1| ≤ x 0 then
        Real.sqrt (x 0 ^ (2 : ℕ) + γ * x 1 ^ (2 : ℕ))
      else
        (x 0 + γ * |x 1|) / Real.sqrt (1 + γ) := by
  -- The theorem is exactly the defining equation of `wolfe_example_function`.
  rfl

/-- The initial point `(gamma, 1)` from Lemma 8.6, expressed in the canonical coordinate model
`EuclideanSpace ℝ (Fin 2)`. -/
def wolfe_initial_point (γ : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  !₂[γ, 1]

-- Proof sketch: unfold `wolfe_initial_point`; the first coordinate of the displayed vector is
-- definitionally `γ`.
/-- The first coordinate of `wolfe_initial_point gamma` is `gamma`. -/
@[simp] theorem wolfe_initial_point_apply_zero (γ : ℝ) :
    wolfe_initial_point γ 0 = γ := by
  -- Reading the first coordinate of the displayed vector returns `γ`.
  rfl

-- Proof sketch: unfold `wolfe_initial_point`; the second coordinate of the displayed vector is
-- definitionally `1`.
/-- The second coordinate of `wolfe_initial_point gamma` is `1`. -/
@[simp] theorem wolfe_initial_point_apply_one (γ : ℝ) :
    wolfe_initial_point γ 1 = 1 := by
  -- Reading the second coordinate of the displayed vector returns `1`.
  rfl

/-- Helper for Lemma 8.6: the Riesz-dual of a two-coordinate Euclidean vector is the matching
linear combination of the two coordinate projections. -/
lemma euclidean_toDual_vec2 (a b : ℝ) :
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin 2)))
        (!₂[a, b] : EuclideanSpace ℝ (Fin 2)) =
      a • EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2) +
        b • EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2) := by
  -- Evaluate both continuous linear maps on an arbitrary vector and compute the dot product.
  ext y
  calc
    ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin 2)))
        (!₂[a, b] : EuclideanSpace ℝ (Fin 2))) y
        = inner ℝ (!₂[a, b] : EuclideanSpace ℝ (Fin 2)) y := by
            simp [InnerProductSpace.toDual_apply_apply]
    _ = a * y 0 + b * y 1 := by
      calc
        inner ℝ (!₂[a, b] : EuclideanSpace ℝ (Fin 2)) y
            = y ⬝ᵥ star (!₂[a, b] : EuclideanSpace ℝ (Fin 2)) := by
                simpa using
                  (EuclideanSpace.inner_eq_star_dotProduct
                    (!₂[a, b] : EuclideanSpace ℝ (Fin 2)) y)
        _ = a * y 0 + b * y 1 := by
          simp [dotProduct, Fin.sum_univ_two, mul_comm]
    _ =
        (a • EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2) +
          b • EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)) y := by
      simp [Pi.smul_apply]

/-- Helper for Lemma 8.6: the quadratic form defining the smooth Wolfe branch has the expected
Euclidean gradient `(2 x₁, 2 γ x₂)`. -/
lemma wolfe_example_quadratic_hasGradientAt {γ : ℝ}
    {x : EuclideanSpace ℝ (Fin 2)} :
    HasGradientAt
      (fun y : EuclideanSpace ℝ (Fin 2) ↦ y 0 ^ (2 : ℕ) + γ * y 1 ^ (2 : ℕ))
      (!₂[(2 : ℝ) * x 0, 2 * γ * x 1]) x := by
  rw [hasGradientAt_iff_hasFDerivAt, euclidean_toDual_vec2]
  let p0 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ := EuclideanSpace.proj (𝕜 := ℝ) 0
  let p1 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ := EuclideanSpace.proj (𝕜 := ℝ) 1
  have hp0 : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 2) ↦ y 0) p0 x := by
    simpa [p0] using p0.hasFDerivAt
  have hp1 : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 2) ↦ y 1) p1 x := by
    simpa [p1] using p1.hasFDerivAt
  have hsq0 :
      HasFDerivAt
        (fun y : EuclideanSpace ℝ (Fin 2) ↦ y 0 ^ (2 : ℕ))
        ((2 * x 0) • p0) x := by
    -- Differentiate the first squared coordinate by the power rule.
    simpa [two_mul, p0] using (hp0.pow 2)
  have hsq1 :
      HasFDerivAt
        (fun y : EuclideanSpace ℝ (Fin 2) ↦ y 1 ^ (2 : ℕ))
        ((2 * x 1) • p1) x := by
    -- Differentiate the second squared coordinate by the same power rule.
    simpa [two_mul, p1] using (hp1.pow 2)
  -- Add the two coordinate contributions to obtain the full quadratic derivative.
  simpa [p0, p1, smul_smul, mul_comm, mul_left_comm, mul_assoc,
    add_comm, add_left_comm, add_assoc] using
    hsq0.add (hsq1.const_mul γ)

/-- Helper for Lemma 8.6: on the strict ellipsoidal branch `|x₂| < x₁`, the Wolfe example
function is smooth with gradient `(x₁, γ x₂) / √(x₁² + γ x₂²)`. -/
lemma wolfe_example_function_hasGradientAt_on_ellipsoidal_region
    {γ : ℝ} (hγ : 0 < γ) {x : EuclideanSpace ℝ (Fin 2)}
    (hx : |x 1| < x 0) (hx0 : x 0 ≠ 0) :
    HasGradientAt (wolfe_example_function γ)
      (!₂[
        x 0 / Real.sqrt (x 0 ^ (2 : ℕ) + γ * x 1 ^ (2 : ℕ)),
        (γ * x 1) / Real.sqrt (x 0 ^ (2 : ℕ) + γ * x 1 ^ (2 : ℕ))]) x := by
  have hquad := wolfe_example_quadratic_hasGradientAt (γ := γ) (x := x)
  have hrad_pos : 0 < x 0 ^ (2 : ℕ) + γ * x 1 ^ (2 : ℕ) := by
    -- The radicand is strictly positive because `x₁ ≠ 0` forces the first squared term positive.
    have hx0sq : 0 < x 0 ^ (2 : ℕ) := by
      exact sq_pos_of_ne_zero hx0
    have hx1sq : 0 ≤ x 1 ^ (2 : ℕ) := sq_nonneg (x 1)
    nlinarith
  have hsqrt :
      HasGradientAt
        (fun y : EuclideanSpace ℝ (Fin 2) ↦
          Real.sqrt (y 0 ^ (2 : ℕ) + γ * y 1 ^ (2 : ℕ)))
        (!₂[
          x 0 / Real.sqrt (x 0 ^ (2 : ℕ) + γ * x 1 ^ (2 : ℕ)),
          (γ * x 1) / Real.sqrt (x 0 ^ (2 : ℕ) + γ * x 1 ^ (2 : ℕ))]) x := by
    rw [hasGradientAt_iff_hasFDerivAt] at hquad ⊢
    rw [euclidean_toDual_vec2]
    have hsqrt := hquad.sqrt (by linarith)
    rw [euclidean_toDual_vec2] at hsqrt
    -- Cancel the factor `2` from the quadratic derivative against the chain-rule denominator.
    simpa [div_eq_mul_inv, smul_add, smul_smul, mul_comm, mul_left_comm, mul_assoc] using
      hsqrt
  have h_eventually :
      wolfe_example_function γ =ᶠ[nhds x]
        (fun y : EuclideanSpace ℝ (Fin 2) ↦
          Real.sqrt (y 0 ^ (2 : ℕ) + γ * y 1 ^ (2 : ℕ))) := by
    have hcont : Continuous fun y : EuclideanSpace ℝ (Fin 2) ↦ y 0 - |y 1| := by
      fun_prop
    have hopen : IsOpen {y : EuclideanSpace ℝ (Fin 2) | 0 < y 0 - |y 1|} := by
      exact isOpen_lt continuous_const hcont
    -- Strict interiority keeps the whole neighborhood on the same smooth branch.
    refine Filter.mem_of_superset (hopen.mem_nhds (sub_pos.2 hx)) ?_
    intro y hy
    have hylt : |y 1| < y 0 := by
      simpa [sub_pos] using hy
    simp [wolfe_example_function, le_of_lt hylt]
  -- Replace the original piecewise function by the smooth branch near `x`.
  exact hsqrt.congr_of_eventuallyEq h_eventually

/-- Helper for Lemma 8.6: along the Wolfe search ray, the first coordinate after stepping by `u`
in the direction `(x₁, γ x₂)` is `(1 - u) x₁`. -/
lemma wolfe_example_ray_step_apply_zero {γ : ℝ} {x : EuclideanSpace ℝ (Fin 2)} {u : ℝ} :
    (x - u • (!₂[x 0, γ * x 1] : EuclideanSpace ℝ (Fin 2))) 0 = (1 - u) * x 0 := by
  -- Compute the first coordinate of the affine ray explicitly.
  simp [sub_eq_add_neg]
  ring

/-- Helper for Lemma 8.6: along the Wolfe search ray, the second coordinate after stepping by `u`
in the direction `(x₁, γ x₂)` is `(1 - γ u) x₂`. -/
lemma wolfe_example_ray_step_apply_one {γ : ℝ} {x : EuclideanSpace ℝ (Fin 2)} {u : ℝ} :
    (x - u • (!₂[x 0, γ * x 1] : EuclideanSpace ℝ (Fin 2))) 1 = (1 - γ * u) * x 1 := by
  -- The second coordinate carries the additional factor `γ` from the search direction.
  simp [sub_eq_add_neg]
  ring

/-- Helper for Lemma 8.6: on the Wolfe ray `x₁ = γ |x₂|`, the one-variable objective obtained by
moving in the direction `(x₁, γ x₂)` has the unique nonnegative minimizer `2 / (γ + 1)`. -/
lemma wolfe_example_directional_objective_minimizer_on_ray
    {γ : ℝ} (hγ : 1 < γ) {x : EuclideanSpace ℝ (Fin 2)}
    (hray : x 0 = γ * |x 1|) (hx : |x 1| < x 0) :
    let g : ℝ → ℝ := fun u ↦
      wolfe_example_function γ (x - u • (!₂[x 0, γ * x 1] : EuclideanSpace ℝ (Fin 2)))
    IsMinOn g (Set.Ici 0) (2 / (γ + 1)) ∧
      ∀ {u : ℝ}, 0 ≤ u → IsMinOn g (Set.Ici 0) u → u = 2 / (γ + 1) := by
  let g : ℝ → ℝ := fun u ↦
    wolfe_example_function γ (x - u • (!₂[x 0, γ * x 1] : EuclideanSpace ℝ (Fin 2)))
  let q : ℝ → ℝ := fun u ↦
    (1 - u) ^ (2 : ℕ) * x 0 ^ (2 : ℕ) + γ * (1 - γ * u) ^ (2 : ℕ) * x 1 ^ (2 : ℕ)
  let uStar : ℝ := 2 / (γ + 1)
  let uBreak : ℝ := (γ + 1) / (2 * γ)
  have hγpos : 0 < γ := by
    linarith
  have hx0_pos : 0 < x 0 := by
    have hxabs_nonneg : 0 ≤ |x 1| := abs_nonneg (x 1)
    nlinarith
  have hx1_ne : x 1 ≠ 0 := by
    intro hx1_zero
    have hx0_zero : x 0 = 0 := by
      simpa [hx1_zero, abs_zero] using hray
    linarith
  have hx1_abs_pos : 0 < |x 1| := abs_pos.2 hx1_ne
  have hsqray : x 0 ^ (2 : ℕ) = γ ^ (2 : ℕ) * x 1 ^ (2 : ℕ) := by
    calc
      x 0 ^ (2 : ℕ) = (γ * |x 1|) ^ (2 : ℕ) := by rw [hray]
      _ = γ ^ (2 : ℕ) * |x 1| ^ (2 : ℕ) := by ring
      _ = γ ^ (2 : ℕ) * x 1 ^ (2 : ℕ) := by rw [sq_abs]
  have huStar_nonneg : 0 ≤ uStar := by
    dsimp [uStar]
    positivity
  have huStar_le_break : uStar ≤ uBreak := by
    have hγ0 : γ ≠ 0 := by
      linarith
    dsimp [uStar, uBreak]
    have h2γ0 : 2 * γ ≠ 0 := by
      positivity
    field_simp [hγ0, h2γ0]
    nlinarith [sq_nonneg (γ - 1)]
  have huBreak_sq : 1 / γ < uBreak ^ (2 : ℕ) := by
    have hγ0 : γ ≠ 0 := by
      linarith
    dsimp [uBreak]
    have h2γ0 : 2 * γ ≠ 0 := by
      positivity
    field_simp [hγ0, h2γ0]
    nlinarith [sq_pos_of_ne_zero (show γ - 1 ≠ 0 by linarith)]
  have hq_nonneg : ∀ u : ℝ, 0 ≤ q u := by
    intro u
    dsimp [q]
    positivity
  have hsmooth_formula :
      ∀ {u : ℝ}, 0 ≤ u → u ≤ uBreak → g u = Real.sqrt (q u) := by
    intro u hu0 huBreak
    have hbranch_scalar :
        |1 - γ * u| ≤ γ * (1 - u) := by
      have hγ0 : γ ≠ 0 := by
        linarith
      have h2γ0 : 2 * γ ≠ 0 := by
        positivity
      refine abs_le.2 ?_
      constructor
      · have huBound : 2 * γ * u ≤ γ + 1 := by
          have huBreak' := huBreak
          dsimp [uBreak] at huBreak'
          field_simp [hγ0, h2γ0] at huBreak'
          nlinarith
        nlinarith
      · nlinarith
    have hbranch :
        |(1 - γ * u) * x 1| ≤ (1 - u) * x 0 := by
      calc
        |(1 - γ * u) * x 1| = |1 - γ * u| * |x 1| := by rw [abs_mul]
        _ ≤ (γ * (1 - u)) * |x 1| := by
          exact mul_le_mul_of_nonneg_right hbranch_scalar (abs_nonneg (x 1))
        _ = (1 - u) * x 0 := by
          rw [hray]
          ring
    have hbranch' :
        |(x - u • (!₂[x 0, γ * x 1] : EuclideanSpace ℝ (Fin 2))) 1| ≤
          (x - u • (!₂[x 0, γ * x 1] : EuclideanSpace ℝ (Fin 2))) 0 := by
      rw [wolfe_example_ray_step_apply_one, wolfe_example_ray_step_apply_zero]
      exact hbranch
    -- Staying below the break point keeps the line-search path on the smooth ellipsoidal branch.
    rw [show g u =
      wolfe_example_function γ (x - u • (!₂[x 0, γ * x 1] : EuclideanSpace ℝ (Fin 2))) by rfl]
    rw [wolfe_example_function_apply, if_pos hbranch']
    rw [wolfe_example_ray_step_apply_zero, wolfe_example_ray_step_apply_one]
    -- Expanding the two coordinates identifies the smooth-branch radicand with `q u`.
    apply congrArg Real.sqrt
    dsimp [q]
    ring
  have hsmooth_gap :
      ∀ u : ℝ, q u - q uStar = γ ^ (2 : ℕ) * (γ + 1) * x 1 ^ (2 : ℕ) * (u - uStar) ^ (2 : ℕ) := by
    intro u
    dsimp [q, uStar]
    rw [hsqray]
    field_simp
    ring
  have hstar_sq :
      q uStar = ((γ - 1) ^ (2 : ℕ) * x 0 ^ (2 : ℕ)) / (γ * (γ + 1)) := by
    have hγ0 : γ ≠ 0 := by
      linarith
    dsimp [q, uStar]
    field_simp [hγ0]
    rw [hsqray]
    ring
  have htail_formula :
      ∀ {u : ℝ}, uBreak < u → g u = ((γ - 1) * x 0 * u) / Real.sqrt (1 + γ) := by
    intro u huTail
    have hu_inv : 1 / γ < u := by
      have huBreak_inv : 1 / γ < uBreak := by
        have hγ0 : γ ≠ 0 := by
          linarith
        dsimp [uBreak]
        have h2γ0 : 2 * γ ≠ 0 := by
          positivity
        field_simp [hγ0, h2γ0]
        nlinarith
      exact lt_trans huBreak_inv huTail
    have habs_scalar : |1 - γ * u| = γ * u - 1 := by
      have hneg : 1 - γ * u < 0 := by
        have hmul : 1 < γ * u := by
          have := mul_lt_mul_of_pos_left hu_inv hγpos
          simpa [div_eq_mul_inv, hγpos.ne'] using this
        exact sub_neg.2 hmul
      rw [abs_of_neg hneg]
      ring
    have hbranch_false :
        ¬ |(1 - γ * u) * x 1| ≤ (1 - u) * x 0 := by
      have hscalar : γ * (1 - u) < γ * u - 1 := by
        have huTail' : γ + 1 < u * (2 * γ) := by
          have h2γ0 : 2 * γ ≠ 0 := by
            positivity
          dsimp [uBreak] at huTail
          field_simp [h2γ0] at huTail
          nlinarith
        nlinarith
      have hlt :
          (1 - u) * x 0 < |(1 - γ * u) * x 1| := by
        calc
          (1 - u) * x 0 = (γ * (1 - u)) * |x 1| := by
            rw [hray]
            ring
          _ < (γ * u - 1) * |x 1| := by
            exact mul_lt_mul_of_pos_right hscalar hx1_abs_pos
          _ = |(1 - γ * u) * x 1| := by
            rw [abs_mul, habs_scalar]
      exact not_le_of_gt hlt
    have hbranch_false' :
        ¬ |(x - u • (!₂[x 0, γ * x 1] : EuclideanSpace ℝ (Fin 2))) 1| ≤
          (x - u • (!₂[x 0, γ * x 1] : EuclideanSpace ℝ (Fin 2))) 0 := by
      rw [wolfe_example_ray_step_apply_one, wolfe_example_ray_step_apply_zero]
      exact hbranch_false
    -- Beyond the break point the path has crossed into the linear branch.
    rw [show g u =
      wolfe_example_function γ (x - u • (!₂[x 0, γ * x 1] : EuclideanSpace ℝ (Fin 2))) by rfl]
    rw [wolfe_example_function_apply, if_neg hbranch_false']
    rw [wolfe_example_ray_step_apply_zero, wolfe_example_ray_step_apply_one]
    rw [abs_mul, habs_scalar, hray]
    field_simp
    ring
  have htail_strict :
      ∀ {u : ℝ}, 0 ≤ u → uBreak < u → g uStar < g u := by
    intro u hu0 huTail
    have hg_u := htail_formula huTail
    have hg_star := hsmooth_formula huStar_nonneg huStar_le_break
    have hu_sq_lower : 1 / γ < u ^ (2 : ℕ) := by
      have huBreak_sq_lt : uBreak ^ (2 : ℕ) < u ^ (2 : ℕ) := by
        have huBreak_nonneg : 0 ≤ uBreak := by
          dsimp [uBreak]
          positivity
        nlinarith
      exact lt_trans huBreak_sq huBreak_sq_lt
    have hcoeff_pos : 0 < (γ - 1) ^ (2 : ℕ) * x 0 ^ (2 : ℕ) := by
      have h1 : 0 < (γ - 1) ^ (2 : ℕ) := sq_pos_of_ne_zero (show γ - 1 ≠ 0 by linarith)
      have h2 : 0 < x 0 ^ (2 : ℕ) := sq_pos_of_ne_zero (show x 0 ≠ 0 by linarith)
      exact mul_pos h1 h2
    have htail_sq :
        (g u) ^ (2 : ℕ) = ((γ - 1) ^ (2 : ℕ) * x 0 ^ (2 : ℕ) * u ^ (2 : ℕ)) / (1 + γ) := by
      have hsqrt_mul : Real.sqrt (1 + γ) * Real.sqrt (1 + γ) = 1 + γ := by
        simpa [sq] using (Real.sq_sqrt (by linarith : 0 ≤ 1 + γ))
      rw [hg_u, div_pow]
      rw [sq, sq, sq]
      rw [hsqrt_mul]
      ring
    have hstar_sq' : (g uStar) ^ (2 : ℕ) =
        ((γ - 1) ^ (2 : ℕ) * x 0 ^ (2 : ℕ)) / (γ * (γ + 1)) := by
      rw [hg_star, Real.sq_sqrt (hq_nonneg uStar), hstar_sq]
    have hsq_lt :
        (g uStar) ^ (2 : ℕ) < (g u) ^ (2 : ℕ) := by
      rw [hstar_sq', htail_sq]
      have hfac : 0 < ((γ - 1) ^ (2 : ℕ) * x 0 ^ (2 : ℕ)) / (1 + γ) := by
        exact div_pos hcoeff_pos (by linarith)
      have hmul := mul_lt_mul_of_pos_left hu_sq_lower hfac
      have hleft :
          ((γ - 1) ^ (2 : ℕ) * x 0 ^ (2 : ℕ)) / (γ * (γ + 1)) =
            ((γ - 1) ^ (2 : ℕ) * x 0 ^ (2 : ℕ)) / (1 + γ) * (1 / γ) := by
        have hγ0 : γ ≠ 0 := by
          linarith
        field_simp [hγ0]
        ring
      have hright :
          ((γ - 1) ^ (2 : ℕ) * x 0 ^ (2 : ℕ)) / (1 + γ) * u ^ (2 : ℕ) =
            ((γ - 1) ^ (2 : ℕ) * x 0 ^ (2 : ℕ) * u ^ (2 : ℕ)) / (1 + γ) := by
        ring
      calc
        ((γ - 1) ^ (2 : ℕ) * x 0 ^ (2 : ℕ)) / (γ * (γ + 1))
            = ((γ - 1) ^ (2 : ℕ) * x 0 ^ (2 : ℕ)) / (1 + γ) * (1 / γ) := hleft
        _ < ((γ - 1) ^ (2 : ℕ) * x 0 ^ (2 : ℕ)) / (1 + γ) * u ^ (2 : ℕ) := hmul
        _ = ((γ - 1) ^ (2 : ℕ) * x 0 ^ (2 : ℕ) * u ^ (2 : ℕ)) / (1 + γ) := hright
    have hstar_nonneg : 0 ≤ g uStar := by
      rw [hg_star]
      exact Real.sqrt_nonneg _
    have hu_nonneg' : 0 ≤ g u := by
      rw [hg_u]
      have hγm1_nonneg : 0 ≤ γ - 1 := by
        linarith
      have hnum_nonneg : 0 ≤ (γ - 1) * x 0 * u := by
        exact mul_nonneg (mul_nonneg hγm1_nonneg (le_of_lt hx0_pos)) hu0
      exact div_nonneg hnum_nonneg (by positivity : 0 ≤ Real.sqrt (1 + γ))
    -- Once the search ray enters the outer branch, the objective value is strictly larger than at
    -- the minimizer candidate `uStar`.
    have habs_lt : |g uStar| < |g u| := by
      simpa using (sq_lt_sq.1 hsq_lt)
    simpa [abs_of_nonneg hstar_nonneg, abs_of_nonneg hu_nonneg'] using habs_lt
  have hstarMin : IsMinOn g (Set.Ici 0) uStar := by
    rw [isMinOn_iff]
    intro u hu0
    by_cases huBreak : u ≤ uBreak
    · have hg_u := hsmooth_formula hu0 huBreak
      have hg_star := hsmooth_formula huStar_nonneg huStar_le_break
      have hgap := hsmooth_gap u
      have hqmin : q uStar ≤ q u := by
        have hnonneg :
            0 ≤ γ ^ (2 : ℕ) * (γ + 1) * x 1 ^ (2 : ℕ) * (u - uStar) ^ (2 : ℕ) := by
          positivity
        nlinarith
      -- On the smooth branch, minimizing `g` is equivalent to minimizing its quadratic radicand.
      calc
        g uStar = Real.sqrt (q uStar) := hg_star
        _ ≤ Real.sqrt (q u) := Real.sqrt_le_sqrt hqmin
        _ = g u := hg_u.symm
    · have huTail : uBreak < u := lt_of_not_ge huBreak
      have hu0' : 0 ≤ u := by
        simpa using hu0
      exact le_of_lt (htail_strict hu0' huTail)
  refine ⟨hstarMin, ?_⟩
  intro u hu0 huMin
  have hleft : g u ≤ g uStar := by
    rw [isMinOn_iff] at huMin
    exact huMin uStar huStar_nonneg
  have hright : g uStar ≤ g u := by
    rw [isMinOn_iff] at hstarMin
    exact hstarMin u hu0
  have hEq : g u = g uStar := le_antisymm hleft hright
  by_cases huBreak : u ≤ uBreak
  · have hg_u := hsmooth_formula hu0 huBreak
    have hg_star := hsmooth_formula huStar_nonneg huStar_le_break
    have hsqrtEq : Real.sqrt (q u) = Real.sqrt (q uStar) := by
      simpa [hg_u, hg_star] using hEq
    have hqEq : q u = q uStar := by
      have hsquare := congrArg (fun z : ℝ ↦ z ^ (2 : ℕ)) hsqrtEq
      simpa [Real.sq_sqrt (hq_nonneg u), Real.sq_sqrt (hq_nonneg uStar)] using hsquare
    have hgap := hsmooth_gap u
    have hcoeff_pos : 0 < γ ^ (2 : ℕ) * (γ + 1) * x 1 ^ (2 : ℕ) := by
      have h1 : 0 < γ ^ (2 : ℕ) := sq_pos_of_ne_zero (show γ ≠ 0 by linarith)
      have h2 : 0 < γ + 1 := by
        linarith
      have h3 : 0 < x 1 ^ (2 : ℕ) := sq_pos_of_ne_zero hx1_ne
      exact mul_pos (mul_pos h1 h2) h3
    have hsquare_zero : (u - uStar) ^ (2 : ℕ) = 0 := by
      have hdiff_zero : q u - q uStar = 0 := by
        rw [hqEq, sub_self]
      have hprod_zero :
          γ ^ (2 : ℕ) * (γ + 1) * x 1 ^ (2 : ℕ) * (u - uStar) ^ (2 : ℕ) = 0 := by
        simpa [hgap] using hdiff_zero
      exact (mul_eq_zero.mp hprod_zero).resolve_left (ne_of_gt hcoeff_pos)
    have hu_eq : u - uStar = 0 := sq_eq_zero_iff.mp hsquare_zero
    have : u = uStar := sub_eq_zero.mp hu_eq
    simpa [uStar] using this
  · have huTail : uBreak < u := lt_of_not_ge huBreak
    have hu0' : 0 ≤ u := by
      simpa using hu0
    have hcontra : False := (ne_of_lt (htail_strict hu0' huTail)) hEq.symm
    exact False.elim hcontra

/-- Helper for Lemma 8.6: on the Wolfe ray, every exact line-search step produces the geometric
update from the source proof. -/
lemma wolfe_example_exact_line_search_update_on_ray
    {γ : ℝ} (hγ : 1 < γ) {x : EuclideanSpace ℝ (Fin 2)}
    (hray : x 0 = γ * |x 1|) (hx : |x 1| < x 0) (hx0 : x 0 ≠ 0) {s : ℝ}
    (hs : s ∈ exact_line_search_stepsizes (wolfe_example_function γ) x) :
    x - s • ∇ (wolfe_example_function γ) x =
      !₂[((γ - 1) / (γ + 1)) * x 0, -((γ - 1) / (γ + 1)) * x 1] := by
  let α : ℝ := 1 / Real.sqrt (x 0 ^ (2 : ℕ) + γ * x 1 ^ (2 : ℕ))
  let v : EuclideanSpace ℝ (Fin 2) := !₂[x 0, γ * x 1]
  let g : ℝ → ℝ := fun u ↦ wolfe_example_function γ (x - u • v)
  let uStar : ℝ := 2 / (γ + 1)
  have hγpos : 0 < γ := by
    linarith
  have hrad_pos : 0 < x 0 ^ (2 : ℕ) + γ * x 1 ^ (2 : ℕ) := by
    have hx0sq : 0 < x 0 ^ (2 : ℕ) := sq_pos_of_ne_zero hx0
    have hx1sq : 0 ≤ x 1 ^ (2 : ℕ) := sq_nonneg (x 1)
    nlinarith
  have hα_pos : 0 < α := by
    dsimp [α]
    exact one_div_pos.2 (Real.sqrt_pos.2 hrad_pos)
  have hgrad :
      ∇ (wolfe_example_function γ) x = α • v := by
    have hHasGrad :=
      wolfe_example_function_hasGradientAt_on_ellipsoidal_region (γ := γ) hγpos hx hx0
    ext i
    fin_cases i
    · -- The first gradient coordinate is the common scaling of `x₁`.
      simp [α, v, hHasGrad.gradient, div_eq_mul_inv, mul_comm, mul_assoc]
    · -- The second coordinate carries the extra factor `γ`.
      simp [α, v, hHasGrad.gradient, div_eq_mul_inv, mul_comm, mul_assoc]
  rcases (mem_exact_line_search_stepsizes_iff.mp hs) with ⟨hs0, hsMin⟩
  have hdirMin : IsMinOn g (Set.Ici 0) (α * s) := by
    rw [isMinOn_iff]
    intro u hu
    have hsDiv : 0 ≤ u / α := by
      exact div_nonneg hu (le_of_lt hα_pos)
    have hsIneq := (isMinOn_iff.mp hsMin) (u / α) hsDiv
    -- Rescale the exact-line-search objective from the actual stepsize `s` to the normalized
    -- directional parameter `u = α s`.
    simpa [g, hgrad, v, div_eq_mul_inv, hα_pos.ne', smul_smul,
      mul_assoc, mul_left_comm, mul_comm] using hsIneq
  have hunique :=
    (wolfe_example_directional_objective_minimizer_on_ray (γ := γ) hγ hray hx).2
      (show 0 ≤ α * s by nlinarith [hα_pos, hs0]) hdirMin
  have hαs : α * s = uStar := hunique
  -- Replacing the exact-line-search parameter by the unique directional minimizer yields the
  -- geometric update from the source proof.
  calc
    x - s • ∇ (wolfe_example_function γ) x = x - (α * s) • v := by
      simp [hgrad, v, α, smul_smul, mul_comm]
    _ = x - uStar • v := by rw [hαs]
    _ = !₂[((γ - 1) / (γ + 1)) * x 0, -((γ - 1) / (γ + 1)) * x 1] := by
      ext i
      fin_cases i
      · simp [uStar, v]
        field_simp
        ring_nf
      · simp [uStar, v]
        field_simp
        ring_nf

theorem wolfe_example_gradient_method_iterate_formula
    {γ : ℝ} (hγ : 1 < γ) {t : ℕ → ℝ}
    (ht :
      ∀ k,
        t k ∈ exact_line_search_stepsizes (wolfe_example_function γ)
          (gradient_method (wolfe_example_function γ) t (wolfe_initial_point γ) k)) :
    ∀ k,
      gradient_method (wolfe_example_function γ) t (wolfe_initial_point γ) k =
        !₂[γ * (((γ - 1) / (γ + 1)) ^ k), (-((γ - 1) / (γ + 1))) ^ k] :=
    by
  let r : ℝ := (γ - 1) / (γ + 1)
  intro k
  induction k with
  | zero =>
  · -- The base iterate is the prescribed initial point `(γ, 1)`.
    simp [gradient_method_zero, wolfe_initial_point]
  | succ k hk =>
    have hγpos : 0 < γ := by
      linarith
    have hr_pos : 0 < r := by
      dsimp [r]
      exact div_pos (by linarith) (by linarith)
    have hk0 :
        gradient_method (wolfe_example_function γ) t (wolfe_initial_point γ) k 0 =
          γ * r ^ k := by
      simpa [r] using
        congrArg (fun y : EuclideanSpace ℝ (Fin 2) ↦ y 0) hk
    have hk1 :
        gradient_method (wolfe_example_function γ) t (wolfe_initial_point γ) k 1 =
          (-r) ^ k := by
      simpa [r] using
        congrArg (fun y : EuclideanSpace ℝ (Fin 2) ↦ y 1) hk
    have hkabs :
        |gradient_method (wolfe_example_function γ) t (wolfe_initial_point γ) k 1| = r ^ k := by
      rw [hk1]
      simp [abs_pow, abs_of_nonneg (le_of_lt hr_pos)]
    have hray :
        gradient_method (wolfe_example_function γ) t (wolfe_initial_point γ) k 0 =
          γ * |gradient_method (wolfe_example_function γ) t (wolfe_initial_point γ) k 1| := by
      rw [hk0, hkabs]
    have hregion :
        |gradient_method (wolfe_example_function γ) t (wolfe_initial_point γ) k 1| <
          gradient_method (wolfe_example_function γ) t (wolfe_initial_point γ) k 0 := by
      rw [hk0, hkabs]
      have hrk_pos : 0 < r ^ k := by
        exact pow_pos hr_pos k
      nlinarith
    have hk0_ne :
        gradient_method (wolfe_example_function γ) t (wolfe_initial_point γ) k 0 ≠ 0 := by
      rw [hk0]
      exact mul_ne_zero (ne_of_gt hγpos) (pow_ne_zero k (ne_of_gt hr_pos))
    have hupdate :=
      wolfe_example_exact_line_search_update_on_ray
        (γ := γ) hγ hray hregion hk0_ne (ht k)
    -- The exact line search gives the one-step recurrence used in the induction.
    calc
      gradient_method (wolfe_example_function γ) t (wolfe_initial_point γ) (k + 1)
          = gradient_method (wolfe_example_function γ) t (wolfe_initial_point γ) k -
              t k • ∇ (wolfe_example_function γ)
                (gradient_method (wolfe_example_function γ) t (wolfe_initial_point γ) k) := by
              simp [gradient_method_succ]
      _ = !₂[r *
            (gradient_method (wolfe_example_function γ) t (wolfe_initial_point γ) k 0),
            -r *
            (gradient_method (wolfe_example_function γ) t (wolfe_initial_point γ) k 1)] := by
        simpa [r] using hupdate
      _ = !₂[r * (γ * r ^ k), -r * ((-r) ^ k)] := by
        rw [hk0, hk1]
      _ = !₂[γ * r ^ (k + 1), (-r) ^ (k + 1)] := by
        ext i
        fin_cases i
        · simp [pow_succ, r, mul_left_comm, mul_comm]
        · simp [pow_succ, r, mul_left_comm, mul_comm]

-- Proof sketch: combine the explicit closed form of the iterates from source clause (c) with the
-- fact from the preceding Wolfe-example analysis that the objective is differentiable away from the
-- nonpositive `x_1`-axis. The closed form keeps every iterate on the rays `x_1 = γ |x_2| > 0`.
/-- Lemma 8.6 (1): source clause (a). The iterates generated by the gradient method with exact line
search for Wolfe's example are differentiability points of the objective. -/
theorem wolfe_example_gradient_method_iterate_differentiableAt
    {γ : ℝ} (hγ : 1 < γ) {t : ℕ → ℝ}
    (ht :
      ∀ k,
        t k ∈ exact_line_search_stepsizes (wolfe_example_function γ)
          (gradient_method (wolfe_example_function γ) t (wolfe_initial_point γ) k)) :
    ∀ k,
      DifferentiableAt ℝ (wolfe_example_function γ)
        (gradient_method (wolfe_example_function γ) t (wolfe_initial_point γ) k) := by
  intro k
  let r : ℝ := (γ - 1) / (γ + 1)
  have hγpos : 0 < γ := by
    linarith
  have hr_pos : 0 < r := by
    have hden : 0 < γ + 1 := by
      linarith
    exact div_pos (by linarith) hden
  have hclosed := wolfe_example_gradient_method_iterate_formula hγ ht k
  rw [hclosed]
  have hxregion :
      |(!₂[γ * (r ^ k), (-r) ^ k] : EuclideanSpace ℝ (Fin 2)) 1| <
        (!₂[γ * (r ^ k), (-r) ^ k] : EuclideanSpace ℝ (Fin 2)) 0 := by
    -- The closed form keeps the iterate strictly inside the smooth branch because `γ > 1`.
    simp [abs_pow, abs_of_nonneg (le_of_lt hr_pos)]
    have hrk_pos : 0 < r ^ k := by
      exact pow_pos hr_pos k
    nlinarith
  have hx0 :
      (!₂[γ * (r ^ k), (-r) ^ k] : EuclideanSpace ℝ (Fin 2)) 0 ≠ 0 := by
    -- The first coordinate is a nonzero positive multiple of `r^k`.
    simp [pow_ne_zero _ (ne_of_gt hr_pos), ne_of_gt hγpos]
  -- On this strict branch, the local gradient formula immediately gives differentiability.
  exact
    (wolfe_example_function_hasGradientAt_on_ellipsoidal_region
      (γ := γ) hγpos hxregion hx0).differentiableAt

-- Proof sketch: use the explicit iterate formula from source clause (c). Its two coordinates are
-- `γ r^k` and `(-r)^k` with `r = (γ - 1) / (γ + 1)`, so `|(x_k)_2| = r^k ≤ γ r^k = (x_k)_1`
-- because `γ > 1`.
/-- Lemma 8.6 (2): source clause (b). Every iterate stays in the region `|x_2| <= x_1`. -/
theorem wolfe_example_gradient_method_iterate_abs_snd_le_fst
    {γ : ℝ} (hγ : 1 < γ) {t : ℕ → ℝ}
    (ht :
      ∀ k,
        t k ∈ exact_line_search_stepsizes (wolfe_example_function γ)
          (gradient_method (wolfe_example_function γ) t (wolfe_initial_point γ) k)) :
    ∀ k,
      |gradient_method (wolfe_example_function γ) t (wolfe_initial_point γ) k 1| ≤
        gradient_method (wolfe_example_function γ) t (wolfe_initial_point γ) k 0 := by
  intro k
  let r : ℝ := (γ - 1) / (γ + 1)
  have hr_pos : 0 < r := by
    have hden : 0 < γ + 1 := by
      linarith
    exact div_pos (by linarith) hden
  have hclosed := wolfe_example_gradient_method_iterate_formula hγ ht k
  have hk0 :
      gradient_method (wolfe_example_function γ) t (wolfe_initial_point γ) k 0 =
        γ * r ^ k := by
    simpa [r] using
      congrArg (fun x : EuclideanSpace ℝ (Fin 2) ↦ x 0) hclosed
  have hk1 :
      gradient_method (wolfe_example_function γ) t (wolfe_initial_point γ) k 1 =
        (-r) ^ k := by
    simpa [r] using
      congrArg (fun x : EuclideanSpace ℝ (Fin 2) ↦ x 1) hclosed
  rw [hk0, hk1]
  calc
    |(-r) ^ k| = r ^ k := by
      simp [abs_pow, abs_of_nonneg (le_of_lt hr_pos)]
    _ ≤ γ * r ^ k := by
      -- Since `γ > 1` and `r^k ≥ 0`, the first coordinate dominates the absolute second one.
      have hrk_nonneg : 0 ≤ r ^ k := by
        exact le_of_lt (pow_pos hr_pos k)
      nlinarith

-- Proof sketch: again use the closed form from source clause (c). The first coordinate is
-- `γ ((γ - 1) / (γ + 1))^k`, and both factors are nonzero when `γ > 1`, so every first coordinate
-- is nonzero.
/-- Lemma 8.6 (3): source clause (b). The first coordinate of every iterate is nonzero. -/
theorem wolfe_example_gradient_method_iterate_fst_ne_zero
    {γ : ℝ} (hγ : 1 < γ) {t : ℕ → ℝ}
    (ht :
      ∀ k,
        t k ∈ exact_line_search_stepsizes (wolfe_example_function γ)
          (gradient_method (wolfe_example_function γ) t (wolfe_initial_point γ) k)) :
    ∀ k,
      gradient_method (wolfe_example_function γ) t (wolfe_initial_point γ) k 0 ≠ 0 := by
  intro k
  let r : ℝ := (γ - 1) / (γ + 1)
  have hγpos : 0 < γ := by
    linarith
  have hr_pos : 0 < r := by
    have hden : 0 < γ + 1 := by
      linarith
    exact div_pos (by linarith) hden
  have hclosed := wolfe_example_gradient_method_iterate_formula hγ ht k
  have hk0 :
      gradient_method (wolfe_example_function γ) t (wolfe_initial_point γ) k 0 =
        γ * r ^ k := by
    simpa [r] using
      congrArg (fun x : EuclideanSpace ℝ (Fin 2) ↦ x 0) hclosed
  rw [hk0]
  -- Both factors in the explicit first coordinate are nonzero.
  exact mul_ne_zero (ne_of_gt hγpos) (pow_ne_zero k (ne_of_gt hr_pos))

-- Proof sketch: prove the displayed formula by induction on `k`. At each step, use the
-- differentiability formula for Wolfe's example on the region `|x_2| <= x_1`, identify the
-- gradient with a positive multiple of `(x_1, γ x_2)`, and show that exact line search selects the
-- minimizer `2 / (γ + 1)`, yielding the recurrence `x_{k+1} = ((γ - 1)/(γ + 1) * x_{k,1},
-- -((γ - 1)/(γ + 1)) * x_{k,2})`.
/-- Lemma 8.6 (4): source clause (c). The gradient method with exact line search on Wolfe's
example has the explicit geometric iterate formula
`x^(k) = (γ ((γ - 1) / (γ + 1))^k, (-(γ - 1) / (γ + 1))^k)`. -/
theorem wolfe_example_gradient_method_iterate_eq_closed_form
    {γ : ℝ} (hγ : 1 < γ) {t : ℕ → ℝ}
    (ht :
      ∀ k,
        t k ∈ exact_line_search_stepsizes (wolfe_example_function γ)
          (gradient_method (wolfe_example_function γ) t (wolfe_initial_point γ) k)) :
    ∀ k,
      gradient_method (wolfe_example_function γ) t (wolfe_initial_point γ) k =
        !₂[γ * (((γ - 1) / (γ + 1)) ^ k), (-((γ - 1) / (γ + 1))) ^ k] := by
  -- The public clause (c) is exactly the helper theorem established above.
  exact wolfe_example_gradient_method_iterate_formula hγ ht

end

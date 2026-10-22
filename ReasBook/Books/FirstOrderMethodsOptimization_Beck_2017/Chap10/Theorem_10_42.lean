/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Lemma_5_7
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_3
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_14
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Assumption_10_31
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_2
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_21
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Theorem_10_16

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open PosReal
open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

variable {f : E → ℝ} {g : E → EReal} {XStar : Set E} {FOpt : ℝ}
variable {Lf σ : PosReal}
variable {x0 xStar : E}

local notation "F" => composite_model_objective f.toEReal g
local notation "κ" => κ(toNNReal Lf, σ)
local notation "t" => Real.sqrt κ

/- Theorem 10.42 is `source-facing` in the strongly-convex fast proximal-gradient API.

Domain sampling in the surrounding chapter identifies:
- `IsFastProximalGradientProblem` as the owner of Assumption 10.31;
- `vfista_x f g x0 Lf σ` from Algorithm 10.14 as the canonical owner of the V-FISTA iterate
  sequence;
- `κ(toNNReal Lf, σ)` from Definition 10.21 as the chapter owner of the condition
  number `κ = L_f / σ`;
- `StrongConvexOn Set.univ (σ : ℝ) f` as the clean library-facing formulation of strong convexity
  for the real-valued smooth term.

Layer triage:
- `source-facing`: the geometric objective-gap estimate for the named V-FISTA iterates `x^k`;
- `core/canonical`: `composite_model_objective`, `vfista_x f g x0 Lf σ`,
  `κ(toNNReal Lf, σ)`, and `StrongConvexOn`;
- `bridge/view`: the optimizer-membership hypothesis `xStar ∈ XStar`.

The theorem is therefore stated directly for the canonical V-FISTA iterate owner, without
introducing a parallel problem-owned wrapper, trajectory package, or existential output layer. -/

section Problem

variable (hproblem : IsFastProximalGradientProblem f g XStar FOpt (toNNReal Lf))

set_option quotPrecheck false in
local notation "xv" =>
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  vfista_x f g x0 Lf σ

set_option quotPrecheck false in
local notation "yv" =>
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  vfista_y f g x0 Lf σ

omit [ProperSpace E] in
/-- Helper for Theorem 10.42: any optimizer in `XStar` attains the composite objective value
`FOpt`. -/
lemma vfista_objective_eq_optimal_value_of_mem_optimal_set
    (hfast : IsFastProximalGradientProblem f g XStar FOpt (toNNReal Lf))
    {x : E} (hx : x ∈ XStar) :
    F x = (FOpt : EReal) := by
  -- Unpack the optimal-set field directly so the helper stays on the owner-level API.
  apply le_antisymm
  · exact hfast.optimal_value_isGLB.2 <| by
      rintro _ ⟨y, rfl⟩
      have hx_opt : x ∈ unconstrained_problem_solutions F := by
        simpa [hfast.optimal_set_eq] using hx
      exact (mem_unconstrained_problem_solutions_iff_forall_le.mp hx_opt) y
  · exact hfast.optimal_value_isGLB.1 ⟨x, rfl⟩

/-- Helper for Theorem 10.42: the global `L_f`-smoothness assumption makes the fixed curvature
`L_f` satisfy the Chapter 10 upper-model test at every real base point. -/
lemma smooth_upper_model_accepts_at_real_point
    [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (hfast : IsFastProximalGradientProblem f g XStar FOpt (toNNReal Lf))
    (y : E) :
    proximal_gradient_backtracking_B2_accepts
      f.toEReal g Lf
      (interior_effective_domain_point_of_real f y) := by
  let yBase := interior_effective_domain_point_of_real f y
  let xNext : E := T[Lf, f.toEReal, g] yBase
  have hy_mem : y ∈ Set.univ := by
    simp
  have hxNext_mem : xNext ∈ Set.univ := by
    simp
  have hdescent :
      f xNext ≤
        f y +
          inner ℝ (∇ f y) (xNext - y) +
          ((Lf : ℝ) / 2) * ‖xNext - y‖ ^ (2 : ℕ) := by
    -- The standing smoothness field provides the upper model at any real base point.
    simpa [xNext, yBase, PosReal.coe_toNNReal, norm_sub_rev] using
      (is_l_smooth_on_descent_lemma
        convex_univ
        hfast.f_smooth
        hy_mem
        hxNext_mem)
  -- Repackage the real-valued upper model as the Chapter 10 B2 acceptance predicate.
  refine (proximal_gradient_backtracking_B2_accepts_iff f.toEReal g Lf yBase).2 ?_
  exact EReal.coe_le_coe_iff.mpr <| by
    simpa [xNext, yBase, Function.toEReal, add_assoc] using hdescent

/-- Helper for Theorem 10.42: the global `L_f`-smoothness assumption makes the fixed curvature
`L_f` satisfy the Chapter 10 upper-model test at every V-FISTA extrapolated point `y^k`. -/
lemma vfista_upper_model_accepts
    [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (hfast : IsFastProximalGradientProblem f g XStar FOpt (toNNReal Lf))
    (k : ℕ) :
    proximal_gradient_backtracking_B2_accepts
      f.toEReal g Lf
      (interior_effective_domain_point_of_real f (vfista_y f g x0 Lf σ k)) := by
  -- Specialize the global smoothness acceptance lemma to the V-FISTA extrapolated point.
  simpa using
    smooth_upper_model_accepts_at_real_point hfast (vfista_y f g x0 Lf σ k)

/-- Helper for Theorem 10.42: the shifted residual used in the source Lyapunov function, written
in the owner-level V-FISTA variables. -/
def vfista_residual_to_optimum
    [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (xStar : E) : ℕ → E
  | 0 => x0 - xStar
  | k + 1 =>
      t • vfista_x f g x0 Lf σ (k + 1) -
        (xStar + (t - 1) • vfista_x f g x0 Lf σ k)

/-- Helper for Theorem 10.42: the affine combination built from `y^k - x^k` is exactly the
shifted residual from the source proof. -/
lemma vfista_residual_to_optimum_eq
    [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (xStar : E) (k : ℕ) :
    vfista_x f g x0 Lf σ k - xStar +
        (t + 1) • (vfista_y f g x0 Lf σ k - vfista_x f g x0 Lf σ k) =
      @vfista_residual_to_optimum
        E _ _ _ f g Lf σ x0 _ _ _ xStar k := by
  cases k with
  | zero =>
      -- At the base index, `y^0 = x^0 = x0`, so the extrapolation term vanishes.
      simp [vfista_residual_to_optimum]
  | succ k =>
      have ht_nonneg : 0 ≤ t := Real.sqrt_nonneg _
      have ht_add_pos : 0 < t + 1 := by
        linarith
      have ht_add_ne : t + 1 ≠ 0 := ht_add_pos.ne'
      have hmomentum :
          vfista_momentum Lf σ = (t - 1) / (t + 1) := by
        have hmomentum' := vfista_momentum_eq Lf σ
        simp [condition_number_eq, PosReal.coe_toNNReal] at hmomentum' ⊢
      have hcoef :
          (t + 1) * ((t - 1) * (t + 1)⁻¹) = t - 1 := by
        field_simp [ht_add_ne]
      -- Expand the V-FISTA extrapolation once and collapse the scalar coefficient.
      rw [vfista_y_succ f g x0 Lf σ k, hmomentum, div_eq_mul_inv]
      -- The remaining identity is pure affine algebra in the Hilbert space.
      rw [smul_sub, smul_add]
      simp_rw [smul_smul]
      rw [hcoef]
      simp [vfista_residual_to_optimum, sub_eq_add_neg, add_assoc]
      module

/-- Helper for Theorem 10.42: every V-FISTA objective gap is nonnegative because `FOpt` is the
greatest lower bound of the composite objective range. -/
lemma vfista_objective_gap_nonneg
    (n : ℕ) :
    0 ≤ F (xv n) - (FOpt : EReal) := by
  have hlower : (FOpt : EReal) ≤ F (xv n) :=
    hproblem.optimal_value_isGLB.1 ⟨xv n, rfl⟩
  -- Convert the optimal-value lower bound into nonnegativity of the shifted objective gap.
  exact (EReal.sub_nonneg (Or.inr (by simp)) (Or.inr (by simp))).2 hlower

/-- Helper for Theorem 10.42: strong convexity of `f` lowers the first-order linearization defect
by the quadratic term `σ ‖x - y‖² / 2`. -/
lemma strong_convexity_linearization_defect_lower_bound_real
    (hproblem : IsFastProximalGradientProblem f g XStar FOpt (toNNReal Lf))
    (hstrong : StrongConvexOn Set.univ (σ : ℝ) f)
    (x y : E) :
    ((σ : ℝ) / 2) * ‖x - y‖ ^ (2 : ℕ) ≤
      f x - f y - inner ℝ (∇ f y) (x - y) := by
  let ψ : E → ℝ := fun z ↦ f z - ((σ : ℝ) / 2) * ‖z‖ ^ (2 : ℕ)
  let line : ℝ → E := AffineMap.lineMap y x
  let φ : ℝ → ℝ := fun s ↦ ψ (line s)
  have hψ_convex : ConvexOn ℝ Set.univ ψ := by
    -- Shift the strongly convex function by the quadratic term from
    -- `strongConvexOn_iff_convex`; this is the source proof's governing object.
    simpa [ψ] using (strongConvexOn_iff_convex.mp hstrong)
  have hφ_convex : ConvexOn ℝ Set.univ φ := by
    -- Restrict the shifted convex function to the segment from `y` to `x`.
    simpa [φ, line] using
      hψ_convex.comp_affineMap (AffineMap.lineMap y x)
  have hy_diff : DifferentiableAt ℝ f y := hproblem.f_smooth.1 y (by simp)
  have hline : HasDerivAt line (x - y) 0 := by
    simpa [line] using
      (show HasDerivAt (AffineMap.lineMap y x) (x - y) (0 : ℝ) from
        AffineMap.hasDerivAt_lineMap)
  have hφf_deriv : HasDerivAt (fun s ↦ f (line s)) (inner ℝ (∇ f y) (x - y)) 0 := by
    -- Differentiate the smooth term along the segment at the base point `y`.
    have hcomp : HasDerivAt (fun s ↦ f (line s)) (fderiv ℝ f y (x - y)) 0 := by
      have hbase : HasFDerivAt f (fderiv ℝ f y) (line 0) := by
        simpa [line] using hy_diff.hasFDerivAt
      simpa [line] using HasFDerivAt.comp_hasDerivAt 0 hbase hline
    have hgrad : fderiv ℝ f y (x - y) = inner ℝ (∇ f y) (x - y) := by
      simpa using
        (show fderiv ℝ f y (x - y) = inner ℝ (∇ f y) (x - y) from
          HasGradientAt.fderiv_apply hy_diff.hasGradientAt)
    simpa [hgrad] using hcomp
  have hφq_deriv :
      HasDerivAt (fun s ↦ ((σ : ℝ) / 2) * ‖line s‖ ^ (2 : ℕ))
        ((σ : ℝ) * inner ℝ y (x - y)) 0 := by
    -- Differentiate the quadratic correction along the same segment.
    have hnorm_sq : HasDerivAt (fun s ↦ ‖line s‖ ^ (2 : ℕ)) (2 * inner ℝ y (x - y)) 0 := by
      simpa [line] using hline.norm_sq
    have hscaled := hnorm_sq.const_mul ((σ : ℝ) / 2)
    convert hscaled using 1
    ring
  have hφ_deriv :
      HasDerivAt φ (inner ℝ (∇ f y) (x - y) - (σ : ℝ) * inner ℝ y (x - y)) 0 := by
    -- The shifted derivative is the smooth derivative minus the quadratic correction.
    simpa [φ, ψ] using hφf_deriv.sub hφq_deriv
  have hsecant :
      inner ℝ (∇ f y) (x - y) - (σ : ℝ) * inner ℝ y (x - y) ≤ slope φ 0 1 := by
    -- Convexity bounds the derivative at the left endpoint by the secant slope.
    exact hφ_convex.le_slope_of_hasDerivAt (by simp) (by simp) zero_lt_one hφ_deriv
  have hsecant' :
      inner ℝ (∇ f y) (x - y) - (σ : ℝ) * inner ℝ y (x - y) ≤
        ψ x - ψ y := by
    simpa [φ, line, slope] using hsecant
  -- Rearrange the shifted support inequality back into the textbook defect lower bound.
  have hsecant'' :
      inner ℝ (∇ f y) (x - y) - (σ : ℝ) * inner ℝ y (x - y) ≤
        (f x - ((σ : ℝ) / 2) * ‖x‖ ^ (2 : ℕ)) -
          (f y - ((σ : ℝ) / 2) * ‖y‖ ^ (2 : ℕ)) := by
    simpa [ψ] using hsecant'
  have hsecant_expanded :
      inner ℝ x (∇ f y) - inner ℝ (∇ f y) y - (σ : ℝ) * (inner ℝ y x - ‖y‖ ^ (2 : ℕ)) ≤
        f x - ((σ : ℝ) / 2) * ‖x‖ ^ (2 : ℕ) -
          (f y - ((σ : ℝ) / 2) * ‖y‖ ^ (2 : ℕ)) := by
    simpa [inner_sub_right, real_inner_self_eq_norm_sq, real_inner_comm] using hsecant''
  have hinner :
      inner ℝ (∇ f y) (x - y) =
        inner ℝ x (∇ f y) - inner ℝ (∇ f y) y := by
    rw [inner_sub_right, real_inner_comm]
  have hnorm :
      ‖x - y‖ ^ (2 : ℕ) =
        ‖x‖ ^ (2 : ℕ) - 2 * inner ℝ y x + ‖y‖ ^ (2 : ℕ) := by
    simpa [real_inner_comm] using (norm_sub_sq_real x y)
  rw [hinner, hnorm]
  linarith

/-- Helper for Theorem 10.42: the linearization defect `ℓ_f(x, y)` dominates
`σ ‖x - y‖² / 2`. -/
lemma strong_convexity_linearization_defect_lower_bound
    (hproblem : IsFastProximalGradientProblem f g XStar FOpt (toNNReal Lf))
    (hstrong : StrongConvexOn Set.univ (σ : ℝ) f)
    (x y : E) :
    ((((σ : ℝ) / 2) * ‖x - y‖ ^ (2 : ℕ) : ℝ) : EReal) ≤
      ℓ[f.toEReal, x, interior_effective_domain_point_of_real f y] := by
  have hreal :
      ((σ : ℝ) / 2) * ‖x - y‖ ^ (2 : ℕ) ≤
        f x - f y - inner ℝ (∇ f y) (x - y) :=
    strong_convexity_linearization_defect_lower_bound_real hproblem hstrong x y
  -- Rewrite the Chapter 10 defect once, then coerce the real inequality into `EReal`.
  rw [prox_gradient_linearization_defect_eq]
  simpa [Function.toEReal] using (EReal.coe_le_coe_iff.mpr hreal)

/-- Helper for Theorem 10.42: combining the accepted upper model with the strong-convex
linearization bound yields the source one-step prox-gap inequality `(10.54)`. -/
lemma vfista_prox_gap_strongly_convex
    (hproblem : IsFastProximalGradientProblem f g XStar FOpt (toNNReal Lf))
    [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (hstrong : StrongConvexOn Set.univ (σ : ℝ) f)
    (x y : E) :
    let yI := interior_effective_domain_point_of_real f y
    let xPlus := T[Lf, f.toEReal, g] yI
    F x - F xPlus ≥
      (((((Lf : ℝ) / 2) * ‖x - xPlus‖ ^ (2 : ℕ) -
          (((Lf : ℝ) - (σ : ℝ)) / 2) * ‖x - y‖ ^ (2 : ℕ) : ℝ)) : EReal) := by
  let yI := interior_effective_domain_point_of_real f y
  let xPlus : E := T[Lf, f.toEReal, g] yI
  have hfund :
      F x - F xPlus ≥
        (((((Lf : ℝ) / 2) * ‖x - xPlus‖ ^ (2 : ℕ) -
            ((Lf : ℝ) / 2) * ‖x - y‖ ^ (2 : ℕ) : ℝ)) : EReal) +
          ℓ[f.toEReal, x, yI] := by
    -- Specialize the fundamental prox-gradient inequality at the real base point `y`.
    simpa [yI, xPlus] using
      (fundamental_prox_grad_inequality
        x yI Lf
        (smooth_upper_model_accepts_at_real_point hproblem y))
  have hlin :
      ((((σ : ℝ) / 2) * ‖x - y‖ ^ (2 : ℕ) : ℝ) : EReal) ≤
        ℓ[f.toEReal, x, yI] := by
    -- Insert the strong-convexity lower bound for the linearization defect.
    simpa [yI] using
      (strong_convexity_linearization_defect_lower_bound hproblem hstrong x y)
  have hinsert :
      (((((Lf : ℝ) / 2) * ‖x - xPlus‖ ^ (2 : ℕ) -
          (((Lf : ℝ) - (σ : ℝ)) / 2) * ‖x - y‖ ^ (2 : ℕ) : ℝ)) : EReal) ≤
        (((((Lf : ℝ) / 2) * ‖x - xPlus‖ ^ (2 : ℕ) -
            ((Lf : ℝ) / 2) * ‖x - y‖ ^ (2 : ℕ) : ℝ)) : EReal) +
          ℓ[f.toEReal, x, yI] := by
    let q0 : ℝ :=
      ((Lf : ℝ) / 2) * ‖x - xPlus‖ ^ (2 : ℕ) -
        ((Lf : ℝ) / 2) * ‖x - y‖ ^ (2 : ℕ)
    have hadd :
        ((((σ : ℝ) / 2) * ‖x - y‖ ^ (2 : ℕ) : ℝ) : EReal) + (q0 : EReal) ≤
          ℓ[f.toEReal, x, yI] + (q0 : EReal) := by
      simpa [add_comm] using add_le_add_right hlin ((q0 : ℝ) : EReal)
    have hadd' :
        (q0 : EReal) + ((((σ : ℝ) / 2) * ‖x - y‖ ^ (2 : ℕ) : ℝ) : EReal) ≤
          (q0 : EReal) + ℓ[f.toEReal, x, yI] := by
      simpa [add_comm, add_left_comm, add_assoc] using hadd
    -- Collapse the added quadratic term into the source coefficient `(L_f - σ) / 2`.
    have hq :
        (((((Lf : ℝ) / 2) * ‖x - xPlus‖ ^ (2 : ℕ) -
            (((Lf : ℝ) - (σ : ℝ)) / 2) * ‖x - y‖ ^ (2 : ℕ) : ℝ)) : EReal) =
          (q0 : EReal) + ((((σ : ℝ) / 2) * ‖x - y‖ ^ (2 : ℕ) : ℝ) : EReal) := by
      rw [← EReal.coe_add]
      congr 1
      dsimp [q0]
      ring_nf
    simpa [hq] using hadd'
  exact le_trans hinsert hfund

/-- Helper for Theorem 10.42: on a nontrivial Hilbert space, comparing the smooth upper model
with the strong-convex lower model forces the smoothness modulus to dominate the strong-convexity
modulus. -/
lemma smoothness_modulus_dominates_strong_convexity_modulus
    [Nontrivial E]
    (hproblem : IsFastProximalGradientProblem f g XStar FOpt (toNNReal Lf))
    (hstrong : StrongConvexOn Set.univ (σ : ℝ) f) :
    (σ : ℝ) ≤ (Lf : ℝ) := by
  obtain ⟨u, hu⟩ : ∃ u : E, u ≠ 0 := exists_ne (0 : E)
  have hdescent :
      f u ≤
        f 0 +
          inner ℝ (∇ f 0) (u - 0) +
            ((Lf : ℝ) / 2) * ‖u - 0‖ ^ (2 : ℕ) := by
    -- The global `L_f`-smoothness field gives the source upper quadratic model at the base point
    -- `0` and the comparison point `u`.
    simpa using
      (is_l_smooth_on_descent_lemma
        convex_univ
        hproblem.f_smooth
        (by simp : (0 : E) ∈ Set.univ)
        (by simp : u ∈ Set.univ))
  have hdefect_upper :
      f u - f 0 - inner ℝ (∇ f 0) (u - 0) ≤
        ((Lf : ℝ) / 2) * ‖u - 0‖ ^ (2 : ℕ) := by
    -- Rearranging the smoothness estimate isolates the textbook linearization defect.
    linarith
  have hdefect_lower :
      ((σ : ℝ) / 2) * ‖u - 0‖ ^ (2 : ℕ) ≤
        f u - f 0 - inner ℝ (∇ f 0) (u - 0) :=
    strong_convexity_linearization_defect_lower_bound_real hproblem hstrong u 0
  have hnorm_sq_pos : 0 < ‖u - 0‖ ^ (2 : ℕ) := by
    -- The witness `u ≠ 0` gives a strictly positive quadratic factor, so the coefficients can be
    -- compared directly.
    simpa using pow_pos (norm_pos_iff.mpr hu) (2 : ℕ)
  nlinarith

/-- Helper for Theorem 10.42: in the nontrivial branch, the source weight `1 / t` is a genuine
convex-combination coefficient. -/
lemma vfista_one_div_t_mem_Icc
    [Nontrivial E]
    (hproblem : IsFastProximalGradientProblem f g XStar FOpt (toNNReal Lf))
    (hstrong : StrongConvexOn Set.univ (σ : ℝ) f) :
    (1 / t : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  have hσ_le_Lf :
      (σ : ℝ) ≤ (Lf : ℝ) :=
    smoothness_modulus_dominates_strong_convexity_modulus hproblem hstrong
  have hκ_nonneg : 0 ≤ κ :=
    condition_number_nonneg (toNNReal Lf) σ
  have ht_sq : t ^ (2 : ℕ) = (Lf : ℝ) / (σ : ℝ) := by
    calc
      t ^ (2 : ℕ) = κ := by
        simpa [pow_two] using (Real.sq_sqrt hκ_nonneg)
      _ = (Lf : ℝ) / (σ : ℝ) := by
        simp [condition_number_eq, PosReal.coe_toNNReal]
  have ht_ge_one : (1 : ℝ) ≤ t := by
    have hσ_ne : (σ : ℝ) ≠ 0 := (PosReal.coe_pos σ).ne'
    have hfrac_ge_one : (1 : ℝ) ≤ (Lf : ℝ) / (σ : ℝ) := by
      field_simp [hσ_ne]
      nlinarith
    have hκ_ge_one : (1 : ℝ) ≤ κ := by
      rw [condition_number_eq, PosReal.coe_toNNReal]
      exact hfrac_ge_one
    change (1 : ℝ) ≤ Real.sqrt κ
    exact Real.one_le_sqrt.mpr hκ_ge_one
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht_ge_one
  refine ⟨one_div_nonneg.mpr (le_of_lt ht_pos), ?_⟩
  -- The upper bound is the reciprocal form of `1 ≤ t`.
  have hrecip : 1 / t ≤ 1 / (1 : ℝ) :=
    one_div_le_one_div_of_le zero_lt_one ht_ge_one
  simpa using hrecip

omit [ProperSpace E] in
/-- Helper for Theorem 10.42: after expanding both norms, the source quadratic-completion step
drops the nonnegative remainder `t (t + 1) ‖d‖²` and yields
`(t + 1) ‖t d + a‖² ≤ t ‖a + (t + 1) d‖² + ‖a‖²`. -/
lemma vfista_completion_norm_identity
    (a d : E) :
    ((t + 1 : ℝ) * ‖t • d + a‖ ^ (2 : ℕ)) ≤
      t * ‖a + (t + 1) • d‖ ^ (2 : ℕ) + ‖a‖ ^ (2 : ℕ) := by
  have ht_nonneg : 0 ≤ t := Real.sqrt_nonneg κ
  have ht_add_nonneg : 0 ≤ t + 1 := by
    linarith
  have hleft :
      ‖t • d + a‖ ^ (2 : ℕ) =
        t ^ (2 : ℕ) * ‖d‖ ^ (2 : ℕ) + 2 * t * inner ℝ a d + ‖a‖ ^ (2 : ℕ) := by
    calc
      ‖t • d + a‖ ^ (2 : ℕ) =
          ‖t • d‖ ^ (2 : ℕ) + 2 * inner ℝ (t • d) a + ‖a‖ ^ (2 : ℕ) := by
        simpa using norm_add_sq_real (t • d) a
      _ = ‖t‖ ^ (2 : ℕ) * ‖d‖ ^ (2 : ℕ) + 2 * (t * inner ℝ a d) + ‖a‖ ^ (2 : ℕ) := by
        rw [norm_smul, real_inner_smul_left, real_inner_comm]
        ring_nf
      _ = t ^ (2 : ℕ) * ‖d‖ ^ (2 : ℕ) + 2 * t * inner ℝ a d + ‖a‖ ^ (2 : ℕ) := by
        simp [mul_assoc]
  have hright :
      ‖a + (t + 1) • d‖ ^ (2 : ℕ) =
        ‖a‖ ^ (2 : ℕ) + 2 * (t + 1) * inner ℝ a d +
          (t + 1) ^ (2 : ℕ) * ‖d‖ ^ (2 : ℕ) := by
    calc
      ‖a + (t + 1) • d‖ ^ (2 : ℕ) =
          ‖a‖ ^ (2 : ℕ) + 2 * inner ℝ a ((t + 1) • d) + ‖(t + 1) • d‖ ^ (2 : ℕ) := by
        simpa using norm_add_sq_real a ((t + 1) • d)
      _ = ‖a‖ ^ (2 : ℕ) + 2 * ((t + 1) * inner ℝ a d) +
          ‖t + 1‖ ^ (2 : ℕ) * ‖d‖ ^ (2 : ℕ) := by
        rw [real_inner_smul_right, norm_smul]
        ring_nf
      _ = ‖a‖ ^ (2 : ℕ) + 2 * (t + 1) * inner ℝ a d +
          (t + 1) ^ (2 : ℕ) * ‖d‖ ^ (2 : ℕ) := by
        simp [mul_assoc]
  let nd : ℝ := ‖d‖ ^ (2 : ℕ)
  let na : ℝ := ‖a‖ ^ (2 : ℕ)
  let iad : ℝ := inner ℝ a d
  have hdrop : 0 ≤ t * (t + 1) * nd := by
    positivity
  -- Expand both squared norms and drop the nonnegative remainder `t (t + 1) ‖d‖²`.
  rw [hleft, hright]
  change (t + 1) * (t ^ (2 : ℕ) * nd + 2 * t * iad + na) ≤
    t * (na + 2 * (t + 1) * iad + (t + 1) ^ (2 : ℕ) * nd) + na
  nlinarith

/-- Helper for Theorem 10.42: the source quadratic-completion step factors through a scalar
comparison between the two squared norms. -/
lemma vfista_quadratic_completion_core
    [Nontrivial E]
    (hproblem : IsFastProximalGradientProblem f g XStar FOpt (toNNReal Lf))
    (hstrong : StrongConvexOn Set.univ (σ : ℝ) f)
    (a d : E) :
    (((Lf : ℝ) - (σ : ℝ)) / 2) * ‖t • d + a‖ ^ (2 : ℕ) ≤
      (((Lf : ℝ) - (σ : ℝ) * t) / 2) * ‖a + (t + 1) • d‖ ^ (2 : ℕ) +
        (((σ : ℝ) * (t - 1)) / 2) * ‖a‖ ^ (2 : ℕ) := by
  have hκ_nonneg : 0 ≤ κ :=
    condition_number_nonneg (toNNReal Lf) σ
  have ht_sq : t ^ (2 : ℕ) = (Lf : ℝ) / (σ : ℝ) := by
    calc
      t ^ (2 : ℕ) = κ := by
        simpa [pow_two] using Real.sq_sqrt hκ_nonneg
      _ = (Lf : ℝ) / (σ : ℝ) := by
        simp [condition_number_eq, PosReal.coe_toNNReal]
  have hσ_ne : (σ : ℝ) ≠ 0 := (PosReal.coe_pos σ).ne'
  have hLf_eq : (Lf : ℝ) = (σ : ℝ) * t ^ (2 : ℕ) := by
    rw [ht_sq]
    field_simp [hσ_ne]
  have hcoef_sub :
      (Lf : ℝ) - (σ : ℝ) = (σ : ℝ) * (t - 1) * (t + 1) := by
    rw [hLf_eq]
    ring
  have hcoef_mix :
      (Lf : ℝ) - (σ : ℝ) * t = (σ : ℝ) * t * (t - 1) := by
    rw [hLf_eq]
    ring
  have hσ_le_Lf :
      (σ : ℝ) ≤ (Lf : ℝ) :=
    smoothness_modulus_dominates_strong_convexity_modulus hproblem hstrong
  have ht_add_pos : 0 < t + 1 := by
    have ht_nonneg : 0 ≤ t := Real.sqrt_nonneg κ
    linarith
  have ht_ge_one : (1 : ℝ) ≤ t := by
    have hfrac_ge_one : (1 : ℝ) ≤ (Lf : ℝ) / (σ : ℝ) := by
      field_simp [hσ_ne]
      nlinarith
    have hκ_ge_one : (1 : ℝ) ≤ κ := by
      rw [condition_number_eq, PosReal.coe_toNNReal]
      exact hfrac_ge_one
    change (1 : ℝ) ≤ Real.sqrt κ
    exact Real.one_le_sqrt.mpr hκ_ge_one
  have ht_sub_nonneg : 0 ≤ t - 1 := by
    linarith
  have hscale_nonneg : 0 ≤ ((σ : ℝ) * (t - 1) / 2) := by
    have hσ_pos : 0 < (σ : ℝ) := PosReal.coe_pos σ
    nlinarith
  -- Route correction: the prior exact identity is false; the source step is the corresponding
  -- inequality obtained after dropping the nonnegative `‖d‖²` remainder.
  have hscaled :
      (((σ : ℝ) * (t - 1)) / 2) * ((t + 1) * ‖t • d + a‖ ^ (2 : ℕ)) ≤
        (((σ : ℝ) * (t - 1)) / 2) *
          (t * ‖a + (t + 1) • d‖ ^ (2 : ℕ) + ‖a‖ ^ (2 : ℕ)) := by
    exact mul_le_mul_of_nonneg_left
      (vfista_completion_norm_identity a d)
      hscale_nonneg
  calc
    (((Lf : ℝ) - (σ : ℝ)) / 2) * ‖t • d + a‖ ^ (2 : ℕ) =
        (((σ : ℝ) * (t - 1)) / 2) * ((t + 1) * ‖t • d + a‖ ^ (2 : ℕ)) := by
      rw [hcoef_sub]
      ring
    _ ≤ (((σ : ℝ) * (t - 1)) / 2) *
          (t * ‖a + (t + 1) • d‖ ^ (2 : ℕ) + ‖a‖ ^ (2 : ℕ)) := hscaled
    _ = (((Lf : ℝ) - (σ : ℝ) * t) / 2) * ‖a + (t + 1) • d‖ ^ (2 : ℕ) +
          (((σ : ℝ) * (t - 1)) / 2) * ‖a‖ ^ (2 : ℕ) := by
      rw [hcoef_mix]
      ring

/-- Helper for Theorem 10.42: the pre-step quadratic term from the source Lyapunov inequality is
dominated by the canonical residual energy after a direct quadratic completion. -/
lemma vfista_prestep_quadratic_completion_bound
    [Nontrivial E]
    [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (hproblem : IsFastProximalGradientProblem f g XStar FOpt (toNNReal Lf))
    (hstrong : StrongConvexOn Set.univ (σ : ℝ) f)
    (xStar : E) (k : ℕ) :
    (((Lf : ℝ) - (σ : ℝ)) / 2) *
        ‖t • (yv k - xv k) + (xv k - xStar)‖ ^ (2 : ℕ) -
      (((σ : ℝ) * (t - 1)) / 2) * ‖xv k - xStar‖ ^ (2 : ℕ) ≤
    (((Lf : ℝ) - (σ : ℝ) * t) / 2) *
      ‖@vfista_residual_to_optimum
          E _ _ _ f g Lf σ x0 _ _ _ xStar k‖ ^ (2 : ℕ) := by
  have hcore :=
    vfista_quadratic_completion_core
      hproblem hstrong (xv k - xStar) (yv k - xv k)
  have hcore' := hcore
  -- Rewrite the completed vector into the source residual, then move the stored `‖x^k - x*‖²`
  -- term across by scalar arithmetic only.
  rw [vfista_residual_to_optimum_eq xStar k] at hcore'
  nlinarith

/-- Helper for Theorem 10.42: strong convexity gives the finite-valued segment upper bound at the
combination point used in the source Lyapunov recursion. -/
lemma vfista_strong_convex_segment_upper_bound_real
    [Nontrivial E]
    (hstrong : StrongConvexOn Set.univ (σ : ℝ) f)
    (k : ℕ) :
    let θ : ℝ := 1 / t
    let z : E := θ • xStar + (1 - θ) • xv k
    f z ≤
      θ * f xStar + (1 - θ) * f (xv k) -
        ((σ : ℝ) / 2) * θ * (1 - θ) * ‖xv k - xStar‖ ^ (2 : ℕ) := by
  let θ : ℝ := 1 / t
  let z : E := θ • xStar + (1 - θ) • xv k
  have hθ_mem :
      θ ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [θ] using
      vfista_one_div_t_mem_Icc hproblem hstrong
  have hθ_nonneg : 0 ≤ θ := hθ_mem.1
  have hone_sub_nonneg : 0 ≤ 1 - θ := sub_nonneg.mpr hθ_mem.2
  have hθ_sum : θ + (1 - θ) = 1 := by
    ring
  have hseg :=
    hstrong.2
      (show xStar ∈ Set.univ by simp)
      (show xv k ∈ Set.univ by simp)
      hθ_nonneg hone_sub_nonneg hθ_sum
  -- Specialize strong convexity to the chapter's combination point and rewrite the penalty term
  -- into the exact `‖x^k - x*‖²` normalization used by the source proof.
  simpa [z, θ, norm_sub_rev, mul_assoc, mul_left_comm, mul_comm] using hseg

omit [ProperSpace E] in
/-- Helper for Theorem 10.42: every optimizer has finite `g`-value, hence belongs to
`effective_domain g`. -/
lemma vfista_optimal_point_mem_effective_domain
    (hproblem : IsFastProximalGradientProblem f g XStar FOpt (toNNReal Lf))
    (hxStar : xStar ∈ XStar) :
    xStar ∈ effective_domain g := by
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  have hxStar_value :
      F xStar = (FOpt : EReal) :=
    vfista_objective_eq_optimal_value_of_mem_optimal_set hproblem hxStar
  have hg_top : g xStar ≠ ⊤ := by
    intro hg_top
    have hFx_top : F xStar = ⊤ := by
      rw [composite_model_objective_apply, Function.toEReal, hg_top]
      simp
    rw [hFx_top] at hxStar_value
    simp at hxStar_value
  exact mem_effective_domain.mpr (lt_top_iff_ne_top.mpr hg_top)

/-- Helper for Theorem 10.42: every positive-index V-FISTA iterate lies in `effective_domain g`
because each iterate is a prox-gradient step. -/
lemma vfista_iterate_succ_mem_effective_domain
    [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (k : ℕ) :
    xv (k + 1) ∈ effective_domain g := by
  -- Rewrite the successor iterate to the prox-gradient point and use the Chapter 10 domain lemma.
  rw [vfista_x_succ f g x0 Lf σ k]
  simpa using
    (prox_grad_step_mem_effective_domain_g (interior_effective_domain_point_of_real f (yv k)) Lf)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E] in
/-- Helper for Theorem 10.42: on `effective_domain g`, the composite objective is the real sum
`f x + g(x).toReal`. -/
lemma vfista_objective_eq_real_of_mem_effective_domain
    [IsProperExtendedRealFunction g]
    {x : E} (hx : x ∈ effective_domain g) :
    F x = (((f x + (g x).toReal : ℝ)) : EReal) := by
  let hg_proper : IsProperExtendedRealFunction g := inferInstance
  have hgx_val :
      g x = (((g x).toReal : ℝ) : EReal) :=
    (EReal.coe_toReal (mem_effective_domain.mp hx).ne (hg_proper.ne_bot x)).symm
  -- Once `g x` is finite, the composite objective is just the sum of two real casts.
  rw [composite_model_objective_apply, Function.toEReal, hgx_val]
  simp

/-- Helper for Theorem 10.42: the source combination point has a finite-valued objective upper
bound on the real line, obtained by combining Jensen for `g` with the strong-convex segment
estimate for `f`. -/
lemma vfista_combination_objective_upper_bound_real
    [Nontrivial E]
    (hproblem : IsFastProximalGradientProblem f g XStar FOpt (toNNReal Lf))
    (hstrong : StrongConvexOn Set.univ (σ : ℝ) f)
    (hxStar : xStar ∈ XStar)
    (k : ℕ) (hxk : xv k ∈ effective_domain g) :
    let θ : ℝ := 1 / t
    let z : E := θ • xStar + (1 - θ) • xv k
    (F z).toReal ≤
      (1 - θ) * ((F (xv k)).toReal - FOpt) + FOpt -
        ((σ : ℝ) / 2) * θ * (1 - θ) * ‖xv k - xStar‖ ^ (2 : ℕ) := by
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  let θ : ℝ := 1 / t
  let z : E := θ • xStar + (1 - θ) • xv k
  have hxStar_eff : xStar ∈ effective_domain g :=
    vfista_optimal_point_mem_effective_domain hproblem hxStar
  have hθ_mem : θ ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [θ] using
      vfista_one_div_t_mem_Icc hproblem hstrong
  have hθ_nonneg : 0 ≤ θ := hθ_mem.1
  have hθ_le_one : θ ≤ 1 := hθ_mem.2
  have hone_sub_nonneg : 0 ≤ 1 - θ := sub_nonneg.mpr hθ_le_one
  have hz_eff : z ∈ effective_domain g := by
    -- Convexity of `g` keeps the source combination point finite-valued.
    exact combo_mem_effective_domain_of_is_convex_function hproblem.g_convex
      hxStar_eff hxk hθ_mem
  have hz_obj :
      F z = (((f z + (g z).toReal : ℝ)) : EReal) :=
    vfista_objective_eq_real_of_mem_effective_domain hz_eff
  have hxk_obj :
      F (xv k) = (((f (xv k) + (g (xv k)).toReal : ℝ)) : EReal) :=
    vfista_objective_eq_real_of_mem_effective_domain hxk
  have hxStar_obj :
      F xStar = (((f xStar + (g xStar).toReal : ℝ)) : EReal) :=
    vfista_objective_eq_real_of_mem_effective_domain hxStar_eff
  have hxStar_value :
      F xStar = (FOpt : EReal) :=
    vfista_objective_eq_optimal_value_of_mem_optimal_set hproblem hxStar
  have hxStar_toReal :
      f xStar + (g xStar).toReal = FOpt := by
    have hxStar_value' :
        (((f xStar + (g xStar).toReal : ℝ)) : EReal) = (FOpt : EReal) := by
      simpa [hxStar_obj] using hxStar_value
    exact EReal.coe_eq_coe_iff.mp hxStar_value'
  have hxk_toReal :
      (F (xv k)).toReal = f (xv k) + (g (xv k)).toReal := by
    rw [hxk_obj, EReal.toReal_coe]
  have hg_convexE :
      g z ≤
        (θ : EReal) * g xStar + ((1 - θ : ℝ) : EReal) * g (xv k) := by
    -- This is the source Jensen inequality for the nonsmooth term.
    simpa [z, θ, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
      (is_convex_function_iff_segment_ineq.mp hproblem.g_convex)
        xStar hxStar_eff (xv k) hxk hθ_mem
  have hg_convex :
      (g z).toReal ≤ θ * (g xStar).toReal + (1 - θ) * (g (xv k)).toReal := by
    have hgxStar_val :
        g xStar = (((g xStar).toReal : ℝ) : EReal) :=
      (EReal.coe_toReal (mem_effective_domain.mp hxStar_eff).ne
        (hproblem.g_proper.ne_bot xStar)).symm
    have hgxk_val :
        g (xv k) = (((g (xv k)).toReal : ℝ) : EReal) :=
      (EReal.coe_toReal (mem_effective_domain.mp hxk).ne
        (hproblem.g_proper.ne_bot _)).symm
    have hgz_val :
        g z = (((g z).toReal : ℝ) : EReal) :=
      (EReal.coe_toReal (mem_effective_domain.mp hz_eff).ne
        (hproblem.g_proper.ne_bot _)).symm
    have hg_convex' :
        (((g z).toReal : ℝ) : EReal) ≤
          (((θ * (g xStar).toReal + (1 - θ) * (g (xv k)).toReal : ℝ)) : EReal) := by
      rw [hgz_val, hgxStar_val, hgxk_val] at hg_convexE
      simpa [EReal.coe_add, EReal.coe_mul] using hg_convexE
    exact EReal.coe_le_coe_iff.mp hg_convex'
  have hf_convex :
      f z ≤
        θ * f xStar + (1 - θ) * f (xv k) -
          ((σ : ℝ) / 2) * θ * (1 - θ) * ‖xv k - xStar‖ ^ (2 : ℕ) := by
    -- Strong convexity contributes the quadratic penalty from the source proof.
    simpa [θ, z] using
      vfista_strong_convex_segment_upper_bound_real hproblem hstrong k
  have hz_toReal :
      (F z).toReal = f z + (g z).toReal := by
    rw [hz_obj, EReal.toReal_coe]
  have hupper_real :
      (F z).toReal ≤
        (1 - θ) * ((F (xv k)).toReal - FOpt) + FOpt -
          ((σ : ℝ) / 2) * θ * (1 - θ) * ‖xv k - xStar‖ ^ (2 : ℕ) := by
    -- Add the smooth and nonsmooth bounds on the finite layer, then substitute `F x* = FOpt`.
    rw [hz_toReal, hxk_toReal]
    nlinarith [hf_convex, hg_convex, hxStar_toReal]
  exact hupper_real

/-- Helper for Theorem 10.42: at any iterate with finite `g`-value, the convex-combination point
`(1 / t) x* + (1 - 1 / t) x^k` satisfies the source objective upper bound coming from strong
convexity of `f` and convexity of `g`. -/
lemma vfista_combination_objective_upper_bound
    [Nontrivial E]
    (hproblem : IsFastProximalGradientProblem f g XStar FOpt (toNNReal Lf))
    (hstrong : StrongConvexOn Set.univ (σ : ℝ) f)
    (hxStar : xStar ∈ XStar)
    (k : ℕ) (hxk : xv k ∈ effective_domain g) :
    let θ : ℝ := 1 / t
    let z : E := θ • xStar + (1 - θ) • xv k
    F z ≤
      ((((1 - θ) * ((F (xv k)).toReal - FOpt) + FOpt -
          ((σ : ℝ) / 2) * θ * (1 - θ) * ‖xv k - xStar‖ ^ (2 : ℕ) : ℝ)) : EReal) := by
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  let θ : ℝ := 1 / t
  let z : E := θ • xStar + (1 - θ) • xv k
  have hxStar_eff : xStar ∈ effective_domain g :=
    vfista_optimal_point_mem_effective_domain hproblem hxStar
  have hθ_mem : θ ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [θ] using
      vfista_one_div_t_mem_Icc hproblem hstrong
  have hz_eff : z ∈ effective_domain g := by
    -- Convexity of `g` keeps the combination point finite-valued.
    exact combo_mem_effective_domain_of_is_convex_function hproblem.g_convex
      hxStar_eff hxk hθ_mem
  have hz_obj :
      F z = (((f z + (g z).toReal : ℝ)) : EReal) :=
    vfista_objective_eq_real_of_mem_effective_domain hz_eff
  have hz_toReal :
      (F z).toReal = f z + (g z).toReal := by
    rw [hz_obj, EReal.toReal_coe]
  have hz_coe :
      F z = ((((F z).toReal : ℝ)) : EReal) := by
    have hz_coe' :
        ((((F z).toReal : ℝ)) : EReal) = F z := by
      rw [hz_obj, EReal.toReal_coe]
    exact hz_coe'.symm
  have hupper_real :
      (F z).toReal ≤
        (1 - θ) * ((F (xv k)).toReal - FOpt) + FOpt -
          ((σ : ℝ) / 2) * θ * (1 - θ) * ‖xv k - xStar‖ ^ (2 : ℕ) := by
    simpa [θ, z] using
      (vfista_combination_objective_upper_bound_real hproblem hproblem hstrong hxStar k hxk)
  have hupperE :
      ((((F z).toReal : ℝ)) : EReal) ≤
        ((((1 - θ) * ((F (xv k)).toReal - FOpt) + FOpt -
            ((σ : ℝ) / 2) * θ * (1 - θ) * ‖xv k - xStar‖ ^ (2 : ℕ) : ℝ)) : EReal) :=
    EReal.coe_le_coe_iff.mpr hupper_real
  -- Repackage the real inequality through the finite-value representation of `F z`.
  calc
    F z = ((((F z).toReal : ℝ)) : EReal) := hz_coe
    _ ≤
        ((((1 - θ) * ((F (xv k)).toReal - FOpt) + FOpt -
            ((σ : ℝ) / 2) * θ * (1 - θ) * ‖xv k - xStar‖ ^ (2 : ℕ) : ℝ)) : EReal) := hupperE

/-- Helper for Theorem 10.42: the source combination point stays in `effective_domain g`
whenever `x^k` is finite-valued. -/
lemma vfista_combination_point_mem_effective_domain
    [Nontrivial E]
    (hproblem : IsFastProximalGradientProblem f g XStar FOpt (toNNReal Lf))
    (hstrong : StrongConvexOn Set.univ (σ : ℝ) f)
    (hxStar : xStar ∈ XStar)
    (k : ℕ) (hxk : xv k ∈ effective_domain g) :
    let θ : ℝ := 1 / t
    let z : E := θ • xStar + (1 - θ) • xv k
    z ∈ effective_domain g := by
  let θ : ℝ := 1 / t
  let z : E := θ • xStar + (1 - θ) • xv k
  have hxStar_eff : xStar ∈ effective_domain g :=
    vfista_optimal_point_mem_effective_domain hproblem hxStar
  have hθ_mem : θ ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [θ] using
      vfista_one_div_t_mem_Icc hproblem hstrong
  -- Convexity of `g` keeps the source combination point finite-valued.
  exact combo_mem_effective_domain_of_is_convex_function hproblem.g_convex
    hxStar_eff hxk hθ_mem

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E] in
/-- Helper for Theorem 10.42: once both objective values are finite, their difference is the
canonical `EReal` cast of the real difference of the `toReal` values. -/
lemma vfista_objective_diff_eq_coe_sub_of_mem_effective_domain
    [IsProperExtendedRealFunction g]
    {x z : E} (hx : x ∈ effective_domain g) (hz : z ∈ effective_domain g) :
    F z - F x = ((((F z).toReal - (F x).toReal : ℝ)) : EReal) := by
  have hz_obj :
      F z = (((f z + (g z).toReal : ℝ)) : EReal) :=
    vfista_objective_eq_real_of_mem_effective_domain hz
  have hx_obj :
      F x = (((f x + (g x).toReal : ℝ)) : EReal) :=
    vfista_objective_eq_real_of_mem_effective_domain hx
  have hz_toReal :
      (F z).toReal = f z + (g z).toReal := by
    rw [hz_obj, EReal.toReal_coe]
  have hx_toReal :
      (F x).toReal = f x + (g x).toReal := by
    rw [hx_obj, EReal.toReal_coe]
  -- Rewrite both objective values through their finite real representatives before using
  -- the canonical `EReal` subtraction rule.
  rw [hz_toReal, hx_toReal, hz_obj, hx_obj]
  simp [EReal.coe_sub]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E] in
/-- Helper for Theorem 10.42: a finite iterate objective gap is the `EReal` cast of the
corresponding real gap to the optimal value `FOpt`. -/
lemma vfista_objective_gap_eq_coe_sub_optimal_value_of_mem_effective_domain
    [IsProperExtendedRealFunction g]
    {x : E} (hx : x ∈ effective_domain g) :
    ((((F x).toReal - FOpt : ℝ)) : EReal) = F x - (FOpt : EReal) := by
  have hx_obj :
      F x = (((f x + (g x).toReal : ℝ)) : EReal) :=
    vfista_objective_eq_real_of_mem_effective_domain hx
  -- Rewrite the finite objective value and simplify the resulting `EReal` subtraction.
  rw [hx_obj, EReal.toReal_coe]
  simp [EReal.coe_sub]

/-- Helper for Theorem 10.42: after scaling by `t`, the source combination-point displacement to
`x^(k+1)` is exactly the post-step residual in the Lyapunov function. -/
lemma vfista_combination_poststep_vector_eq
    [Nontrivial E]
    [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (hproblem : IsFastProximalGradientProblem f g XStar FOpt (toNNReal Lf))
    (hstrong : StrongConvexOn Set.univ (σ : ℝ) f)
    (xStar : E) (k : ℕ) :
    let z : E := (1 / t) • xStar + (1 - 1 / t) • xv k
    (-t) • (z - xv (k + 1)) =
      @vfista_residual_to_optimum
        E _ _ _ f g Lf σ x0 _ _ _ xStar (k + 1) := by
  let z : E := (1 / t) • xStar + (1 - 1 / t) • xv k
  have hσ_le_Lf :
      (σ : ℝ) ≤ (Lf : ℝ) :=
    smoothness_modulus_dominates_strong_convexity_modulus hproblem hstrong
  have ht_ge_one : (1 : ℝ) ≤ t := by
    have hσ_ne : (σ : ℝ) ≠ 0 := (PosReal.coe_pos σ).ne'
    have hfrac_ge_one : (1 : ℝ) ≤ (Lf : ℝ) / (σ : ℝ) := by
      field_simp [hσ_ne]
      nlinarith
    have hκ_ge_one : (1 : ℝ) ≤ κ := by
      rw [condition_number_eq, PosReal.coe_toNNReal]
      exact hfrac_ge_one
    change (1 : ℝ) ≤ Real.sqrt κ
    exact Real.one_le_sqrt.mpr hκ_ge_one
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht_ge_one
  have ht_ne : t ≠ 0 := ht_pos.ne'
  have hmul_xStar : (-t : ℝ) * (1 / t) = -1 := by
    field_simp [ht_ne]
  have hmul_xk : (-t : ℝ) * (1 - 1 / t) = 1 - t := by
    field_simp [ht_ne]
    ring
  -- Expand the combination point and collapse the scalar coefficients from `(10.55)`.
  dsimp [z]
  simp_rw [condition_number_eq, PosReal.coe_toNNReal] at hmul_xStar hmul_xk ⊢
  rw [sub_eq_add_neg, smul_add, smul_add, smul_smul, smul_smul]
  rw [hmul_xStar, hmul_xk]
  simp [vfista_residual_to_optimum, sub_eq_add_neg, add_assoc]
  module

/-- Helper for Theorem 10.42: after scaling by `t`, the source combination-point displacement to
`y^k` is exactly the pre-step vector appearing in `(10.56)`. -/
lemma vfista_combination_prestep_vector_eq
    [Nontrivial E]
    (hproblem : IsFastProximalGradientProblem f g XStar FOpt (toNNReal Lf))
    (hstrong : StrongConvexOn Set.univ (σ : ℝ) f)
    (xStar : E) (k : ℕ) :
    let z : E := (1 / t) • xStar + (1 - 1 / t) • xv k
    (-t) • (z - yv k) =
      t • (yv k - xv k) + (xv k - xStar) := by
  let z : E := (1 / t) • xStar + (1 - 1 / t) • xv k
  have hσ_le_Lf :
      (σ : ℝ) ≤ (Lf : ℝ) :=
    smoothness_modulus_dominates_strong_convexity_modulus hproblem hstrong
  have ht_ge_one : (1 : ℝ) ≤ t := by
    have hσ_ne : (σ : ℝ) ≠ 0 := (PosReal.coe_pos σ).ne'
    have hfrac_ge_one : (1 : ℝ) ≤ (Lf : ℝ) / (σ : ℝ) := by
      field_simp [hσ_ne]
      nlinarith
    have hκ_ge_one : (1 : ℝ) ≤ κ := by
      rw [condition_number_eq, PosReal.coe_toNNReal]
      exact hfrac_ge_one
    change (1 : ℝ) ≤ Real.sqrt κ
    exact Real.one_le_sqrt.mpr hκ_ge_one
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht_ge_one
  have ht_ne : t ≠ 0 := ht_pos.ne'
  have hmul_xStar : (-t : ℝ) * (1 / t) = -1 := by
    field_simp [ht_ne]
  have hmul_xk : (-t : ℝ) * (1 - 1 / t) = 1 - t := by
    field_simp [ht_ne]
    ring
  -- Expand the combination point and regroup the affine terms into the source pre-step vector.
  dsimp [z]
  simp_rw [condition_number_eq, PosReal.coe_toNNReal] at hmul_xStar hmul_xk ⊢
  rw [sub_eq_add_neg, smul_add, smul_add, smul_smul, smul_smul]
  rw [hmul_xStar, hmul_xk]
  simp [sub_eq_add_neg, add_assoc]
  module

/-- Helper for Theorem 10.42: the post-step quadratic term from `(10.55)` is exactly the norm of
the Lyapunov residual at index `k + 1`. -/
lemma vfista_poststep_norm_scaled
    [Nontrivial E]
    [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (hproblem : IsFastProximalGradientProblem f g XStar FOpt (toNNReal Lf))
    (hstrong : StrongConvexOn Set.univ (σ : ℝ) f)
    (xStar : E) (k : ℕ) :
    let z : E := (1 / t) • xStar + (1 - 1 / t) • xv k
    t ^ (2 : ℕ) * ‖z - xv (k + 1)‖ ^ (2 : ℕ) =
      ‖@vfista_residual_to_optimum
          E _ _ _ f g Lf σ x0 _ _ _ xStar (k + 1)‖ ^ (2 : ℕ) := by
  let z : E := (1 / t) • xStar + (1 - 1 / t) • xv k
  have ht_nonneg : 0 ≤ t := Real.sqrt_nonneg κ
  have hvec :
      (-t) • (z - xv (k + 1)) =
        @vfista_residual_to_optimum
          E _ _ _ f g Lf σ x0 _ _ _ xStar (k + 1) := by
    simpa [z] using
      (vfista_combination_poststep_vector_eq hproblem hproblem hstrong xStar k)
  have hnorm :
      t * ‖z - xv (k + 1)‖ =
        ‖@vfista_residual_to_optimum
            E _ _ _ f g Lf σ x0 _ _ _ xStar (k + 1)‖ := by
    -- Taking norms turns the affine identity into the scaled norm equality.
    have hsqrt_nonneg : 0 ≤ Real.sqrt ((Lf : ℝ) / (σ : ℝ)) := by
      positivity
    simpa [condition_number_eq, PosReal.coe_toNNReal, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hsqrt_nonneg] using
      congrArg (fun v ↦ ‖v‖) hvec
  calc
    t ^ (2 : ℕ) * ‖z - xv (k + 1)‖ ^ (2 : ℕ) = (t * ‖z - xv (k + 1)‖) ^ (2 : ℕ) := by
      ring
    _ = ‖@vfista_residual_to_optimum
            E _ _ _ f g Lf σ x0 _ _ _ xStar (k + 1)‖ ^ (2 : ℕ) := by
      rw [hnorm]

/-- Helper for Theorem 10.42: the pre-step quadratic term from `(10.55)` is exactly the norm of
the pre-step vector in `(10.56)` after scaling by `t`. -/
lemma vfista_prestep_norm_scaled
    [Nontrivial E]
    (hproblem : IsFastProximalGradientProblem f g XStar FOpt (toNNReal Lf))
    (hstrong : StrongConvexOn Set.univ (σ : ℝ) f)
    (xStar : E) (k : ℕ) :
    let z : E := (1 / t) • xStar + (1 - 1 / t) • xv k
    t ^ (2 : ℕ) * ‖z - yv k‖ ^ (2 : ℕ) =
      ‖t • (yv k - xv k) + (xv k - xStar)‖ ^ (2 : ℕ) := by
  let z : E := (1 / t) • xStar + (1 - 1 / t) • xv k
  have ht_nonneg : 0 ≤ t := Real.sqrt_nonneg κ
  have hvec :
      (-t) • (z - yv k) =
        t • (yv k - xv k) + (xv k - xStar) := by
    simpa [z] using
      (vfista_combination_prestep_vector_eq hproblem hproblem hstrong xStar k)
  have hnorm :
      t * ‖z - yv k‖ =
        ‖t • (yv k - xv k) + (xv k - xStar)‖ := by
    -- Taking norms turns the affine identity into the scaled norm equality.
    have hsqrt_nonneg : 0 ≤ Real.sqrt ((Lf : ℝ) / (σ : ℝ)) := by
      positivity
    simpa [condition_number_eq, PosReal.coe_toNNReal, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hsqrt_nonneg] using
      congrArg (fun v ↦ ‖v‖) hvec
  calc
    t ^ (2 : ℕ) * ‖z - yv k‖ ^ (2 : ℕ) = (t * ‖z - yv k‖) ^ (2 : ℕ) := by
      ring
    _ = ‖t • (yv k - xv k) + (xv k - xStar)‖ ^ (2 : ℕ) := by
      rw [hnorm]

/-- Helper for Theorem 10.42: once both endpoints of the prox-gap estimate are finite-valued,
the source inequality `(10.54)` can be read as an ordinary real inequality. -/
lemma vfista_prox_gap_real_of_finite_values
    [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (hproblem : IsFastProximalGradientProblem f g XStar FOpt (toNNReal Lf))
    (hstrong : StrongConvexOn Set.univ (σ : ℝ) f)
    (x y : E) (hx : x ∈ effective_domain g) :
    let yI := interior_effective_domain_point_of_real f y
    let xPlus : E := T[Lf, f.toEReal, g] yI
    (((Lf : ℝ) / 2) * ‖x - xPlus‖ ^ (2 : ℕ) -
        (((Lf : ℝ) - (σ : ℝ)) / 2) * ‖x - y‖ ^ (2 : ℕ)) ≤
      (F x).toReal - (F xPlus).toReal := by
  let yI := interior_effective_domain_point_of_real f y
  let xPlus : E := T[Lf, f.toEReal, g] yI
  have hxPlus :
      xPlus ∈ effective_domain g := by
    -- The prox-gradient step at a real base point always lands in `effective_domain g`.
    simpa [xPlus, yI] using
      (prox_grad_step_mem_effective_domain_g yI Lf)
  have hgapE :
      (((((Lf : ℝ) / 2) * ‖x - xPlus‖ ^ (2 : ℕ) -
          (((Lf : ℝ) - (σ : ℝ)) / 2) * ‖x - y‖ ^ (2 : ℕ) : ℝ)) : EReal) ≤
        F x - F xPlus := by
    -- This is exactly the owner-level prox-gap inequality `(10.54)` specialized at `x` and `y`.
    simpa [yI, xPlus] using
      (vfista_prox_gap_strongly_convex hproblem hstrong x y)
  have hgapE' := hgapE
  -- Rewrite the finite objective difference into the canonical real subtraction before stripping
  -- the final coercion.
  rw [vfista_objective_diff_eq_coe_sub_of_mem_effective_domain hxPlus hx] at hgapE'
  -- Strip the final coercion to recover the real inequality used in `(10.56)`.
  exact EReal.coe_le_coe_iff.mp hgapE'

/-- Helper for Theorem 10.42: after scaling `(1 - 1 / t)` by `t²`, the source coefficient
becomes `t (t - 1)`. -/
lemma vfista_scaled_objective_gap_coefficient
    [Nontrivial E]
    (hproblem : IsFastProximalGradientProblem f g XStar FOpt (toNNReal Lf))
    (hstrong : StrongConvexOn Set.univ (σ : ℝ) f) :
    t ^ (2 : ℕ) * (1 - 1 / t) = t * (t - 1) := by
  have hσ_le_Lf :
      (σ : ℝ) ≤ (Lf : ℝ) :=
    smoothness_modulus_dominates_strong_convexity_modulus hproblem hstrong
  have hσ_ne : (σ : ℝ) ≠ 0 := (PosReal.coe_pos σ).ne'
  have hfrac_ge_one : (1 : ℝ) ≤ (Lf : ℝ) / (σ : ℝ) := by
    field_simp [hσ_ne]
    nlinarith
  have hκ_ge_one : (1 : ℝ) ≤ κ := by
    rw [condition_number_eq, PosReal.coe_toNNReal]
    exact hfrac_ge_one
  have ht_ge_one : (1 : ℝ) ≤ t := by
    change (1 : ℝ) ≤ Real.sqrt κ
    exact Real.one_le_sqrt.mpr hκ_ge_one
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht_ge_one
  have ht_ne : t ≠ 0 := ht_pos.ne'
  -- Clear the reciprocal `1 / t` using the positivity of `t`.
  field_simp [ht_ne]

/-- Helper for Theorem 10.42: after scaling the strong-convexity penalty in `(10.55)` by `t²`,
the source coefficient becomes `σ (t - 1) / 2`. -/
lemma vfista_scaled_strong_convexity_coefficient
    [Nontrivial E]
    (hproblem : IsFastProximalGradientProblem f g XStar FOpt (toNNReal Lf))
    (hstrong : StrongConvexOn Set.univ (σ : ℝ) f) :
    t ^ (2 : ℕ) * (((σ : ℝ) / 2) * (1 / t) * (1 - 1 / t)) =
      (((σ : ℝ) * (t - 1)) / 2) := by
  have hσ_le_Lf :
      (σ : ℝ) ≤ (Lf : ℝ) :=
    smoothness_modulus_dominates_strong_convexity_modulus hproblem hstrong
  have hσ_ne : (σ : ℝ) ≠ 0 := (PosReal.coe_pos σ).ne'
  have hfrac_ge_one : (1 : ℝ) ≤ (Lf : ℝ) / (σ : ℝ) := by
    field_simp [hσ_ne]
    nlinarith
  have hκ_ge_one : (1 : ℝ) ≤ κ := by
    rw [condition_number_eq, PosReal.coe_toNNReal]
    exact hfrac_ge_one
  have ht_ge_one : (1 : ℝ) ≤ t := by
    change (1 : ℝ) ≤ Real.sqrt κ
    exact Real.one_le_sqrt.mpr hκ_ge_one
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht_ge_one
  have ht_ne : t ≠ 0 := ht_pos.ne'
  -- Clear the reciprocal `1 / t` before normalizing the scalar coefficient.
  field_simp [ht_ne]

/-- Helper for Theorem 10.42: this is the real-valued Lyapunov balance corresponding to the
textbook inequality `(10.56)`, obtained by combining the prox-gap lower bound with the
strong-convexity upper bound on the source combination point. -/
lemma vfista_lyapunov_balance_real
    [Nontrivial E]
    [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (hproblem : IsFastProximalGradientProblem f g XStar FOpt (toNNReal Lf))
    (hstrong : StrongConvexOn Set.univ (σ : ℝ) f)
    (hxStar : xStar ∈ XStar)
    (k : ℕ) (hxk : xv k ∈ effective_domain g) :
    let vR : ℕ → ℝ := fun n ↦ (F (xv n)).toReal - FOpt
    t ^ (2 : ℕ) * vR (k + 1) +
        ((Lf : ℝ) / 2) *
          ‖@vfista_residual_to_optimum
              E _ _ _ f g Lf σ x0 _ _ _ xStar (k + 1)‖ ^ (2 : ℕ) ≤
      t * (t - 1) * vR k +
        (((Lf : ℝ) - (σ : ℝ)) / 2) * ‖t • (yv k - xv k) + (xv k - xStar)‖ ^ (2 : ℕ) -
          (((σ : ℝ) * (t - 1)) / 2) * ‖xv k - xStar‖ ^ (2 : ℕ) := by
  let vR : ℕ → ℝ := fun n ↦ (F (xv n)).toReal - FOpt
  let θ : ℝ := 1 / t
  let z : E := θ • xStar + (1 - θ) • xv k
  have hz_eff : z ∈ effective_domain g := by
    -- The source comparison point is finite-valued, so the prox-gap inequality can be read on `ℝ`.
    simpa [θ, z] using
      (vfista_combination_point_mem_effective_domain hproblem hproblem hstrong hxStar k hxk)
  have hprox :
      ((Lf : ℝ) / 2) * ‖z - xv (k + 1)‖ ^ (2 : ℕ) -
          (((Lf : ℝ) - (σ : ℝ)) / 2) * ‖z - yv k‖ ^ (2 : ℕ) ≤
        (F z).toReal - (F (xv (k + 1))).toReal := by
    -- Specialize `(10.54)` at the source combination point and rewrite the prox step as `x^(k+1)`.
    simpa [z, θ, vfista_x_succ] using
      (vfista_prox_gap_real_of_finite_values hproblem hstrong z (yv k) hz_eff)
  have hupper :
      (F z).toReal ≤
        (1 - θ) * vR k + FOpt -
          ((σ : ℝ) / 2) * θ * (1 - θ) * ‖xv k - xStar‖ ^ (2 : ℕ) := by
    -- The strong-convex combination bound gives the real upper estimate for `F z`.
    simpa [vR, θ, z] using
      (vfista_combination_objective_upper_bound_real
        hproblem hproblem hstrong hxStar k hxk)
  have hupper_sub :
      (F z).toReal - (F (xv (k + 1))).toReal ≤
        (1 - 1 / t) * vR k - vR (k + 1) -
          ((σ : ℝ) / 2) * (1 / t) * (1 - 1 / t) * ‖xv k - xStar‖ ^ (2 : ℕ) := by
    -- Rewrite the upper estimate for `F z` against the shifted gap `vR (k + 1)`.
    dsimp [vR, θ] at hupper ⊢
    linarith
  have hraw :
      ((Lf : ℝ) / 2) * ‖z - xv (k + 1)‖ ^ (2 : ℕ) -
          (((Lf : ℝ) - (σ : ℝ)) / 2) * ‖z - yv k‖ ^ (2 : ℕ) ≤
        (1 - 1 / t) * vR k - vR (k + 1) -
          ((σ : ℝ) / 2) * (1 / t) * (1 - 1 / t) * ‖xv k - xStar‖ ^ (2 : ℕ) :=
    le_trans hprox hupper_sub
  have hscaled :
      t ^ (2 : ℕ) *
          (((Lf : ℝ) / 2) * ‖z - xv (k + 1)‖ ^ (2 : ℕ) -
            (((Lf : ℝ) - (σ : ℝ)) / 2) * ‖z - yv k‖ ^ (2 : ℕ)) ≤
        t ^ (2 : ℕ) *
          ((1 - 1 / t) * vR k - vR (k + 1) -
            ((σ : ℝ) / 2) * (1 / t) * (1 - 1 / t) * ‖xv k - xStar‖ ^ (2 : ℕ)) := by
    -- Scale the raw inequality by `t²`, matching the source normalization in `(10.56)`.
    exact mul_le_mul_of_nonneg_left hraw (by positivity)
  have hpost :
      t ^ (2 : ℕ) * ‖z - xv (k + 1)‖ ^ (2 : ℕ) =
        ‖@vfista_residual_to_optimum
            E _ _ _ f g Lf σ x0 _ _ _ xStar (k + 1)‖ ^ (2 : ℕ) := by
    -- Rewrite the post-step norm term into the Lyapunov residual at index `k + 1`.
    simpa [θ, z] using
      (vfista_poststep_norm_scaled hproblem hproblem hstrong xStar k)
  have hpre :
      t ^ (2 : ℕ) * ‖z - yv k‖ ^ (2 : ℕ) =
        ‖t • (yv k - xv k) + (xv k - xStar)‖ ^ (2 : ℕ) := by
    -- Rewrite the pre-step norm term into the vector appearing in the source balance.
    simpa [θ, z] using
      (vfista_prestep_norm_scaled hproblem hproblem hstrong xStar k)
  have hcoef_gap :
      t ^ (2 : ℕ) * (1 - 1 / t) = t * (t - 1) :=
    vfista_scaled_objective_gap_coefficient hproblem hstrong
  have hcoef_sigma :
      t ^ (2 : ℕ) * (((σ : ℝ) / 2) * (1 / t) * (1 - 1 / t)) =
        (((σ : ℝ) * (t - 1)) / 2) :=
    vfista_scaled_strong_convexity_coefficient hproblem hstrong
  -- Route correction: isolate the scalar coefficient transports and the two scaled norm rewrites
  -- before the final arithmetic step, instead of asking `whnf` to normalize the whole inequality.
  have hscaled' :
      ((Lf : ℝ) / 2) * (t ^ (2 : ℕ) * ‖z - xv (k + 1)‖ ^ (2 : ℕ)) -
          (((Lf : ℝ) - (σ : ℝ)) / 2) * (t ^ (2 : ℕ) * ‖z - yv k‖ ^ (2 : ℕ)) ≤
        (t ^ (2 : ℕ) * (1 - 1 / t)) * vR k - t ^ (2 : ℕ) * vR (k + 1) -
          (t ^ (2 : ℕ) * (((σ : ℝ) / 2) * (1 / t) * (1 - 1 / t))) *
            ‖xv k - xStar‖ ^ (2 : ℕ) := by
    -- Expand the scaled inequality so each transported term can be rewritten separately.
    simpa [sub_eq_add_neg, mul_add, add_mul, mul_sub, sub_mul, mul_assoc, mul_left_comm, mul_comm]
      using hscaled
  have hrewritten :
      ((Lf : ℝ) / 2) *
          ‖@vfista_residual_to_optimum
              E _ _ _ f g Lf σ x0 _ _ _ xStar (k + 1)‖ ^ (2 : ℕ) -
          (((Lf : ℝ) - (σ : ℝ)) / 2) * ‖t • (yv k - xv k) + (xv k - xStar)‖ ^ (2 : ℕ) ≤
        t * (t - 1) * vR k - t ^ (2 : ℕ) * vR (k + 1) -
          (((σ : ℝ) * (t - 1)) / 2) * ‖xv k - xStar‖ ^ (2 : ℕ) := by
    -- Rewrite the scaled norms and scalar coefficients into the exact source-facing terms.
    have hrewritten' := hscaled'
    rw [hpost, hpre, hcoef_gap, hcoef_sigma] at hrewritten'
    exact hrewritten'
  have hfinal :
      t ^ (2 : ℕ) * vR (k + 1) +
          ((Lf : ℝ) / 2) *
            ‖@vfista_residual_to_optimum
                E _ _ _ f g Lf σ x0 _ _ _ xStar (k + 1)‖ ^ (2 : ℕ) ≤
        t * (t - 1) * vR k +
          (((Lf : ℝ) - (σ : ℝ)) / 2) * ‖t • (yv k - xv k) + (xv k - xStar)‖ ^ (2 : ℕ) -
            (((σ : ℝ) * (t - 1)) / 2) * ‖xv k - xStar‖ ^ (2 : ℕ) := by
    -- Move the two transported quadratic terms to their final sides.
    linarith
  simpa [vR] using hfinal

/-- Helper for Theorem 10.42: applying the quadratic-completion bound to the raw balance
transforms `(10.56)` into the completed Lyapunov inequality `(10.57)`. -/
lemma vfista_lyapunov_completed_real
    [Nontrivial E]
    [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (hproblem : IsFastProximalGradientProblem f g XStar FOpt (toNNReal Lf))
    (hstrong : StrongConvexOn Set.univ (σ : ℝ) f)
    (hxStar : xStar ∈ XStar)
    (k : ℕ) (hxk : xv k ∈ effective_domain g) :
    let vR : ℕ → ℝ := fun n ↦ (F (xv n)).toReal - FOpt
    t ^ (2 : ℕ) * vR (k + 1) +
        ((Lf : ℝ) / 2) *
          ‖@vfista_residual_to_optimum
              E _ _ _ f g Lf σ x0 _ _ _ xStar (k + 1)‖ ^ (2 : ℕ) ≤
      t * (t - 1) * vR k +
        (((Lf : ℝ) - (σ : ℝ) * t) / 2) *
          ‖@vfista_residual_to_optimum
              E _ _ _ f g Lf σ x0 _ _ _ xStar k‖ ^ (2 : ℕ) := by
  let vR : ℕ → ℝ := fun n ↦ (F (xv n)).toReal - FOpt
  have hbalance :
      t ^ (2 : ℕ) * vR (k + 1) +
          ((Lf : ℝ) / 2) *
            ‖@vfista_residual_to_optimum
                E _ _ _ f g Lf σ x0 _ _ _ xStar (k + 1)‖ ^ (2 : ℕ) ≤
        t * (t - 1) * vR k +
          (((Lf : ℝ) - (σ : ℝ)) / 2) * ‖t • (yv k - xv k) + (xv k - xStar)‖ ^ (2 : ℕ) -
            (((σ : ℝ) * (t - 1)) / 2) * ‖xv k - xStar‖ ^ (2 : ℕ) := by
    -- First use the raw Lyapunov balance `(10.56)`.
    simpa [vR] using
      (vfista_lyapunov_balance_real
        hproblem hproblem hstrong hxStar k hxk)
  have hcomplete :
      (((Lf : ℝ) - (σ : ℝ)) / 2) * ‖t • (yv k - xv k) + (xv k - xStar)‖ ^ (2 : ℕ) -
          (((σ : ℝ) * (t - 1)) / 2) * ‖xv k - xStar‖ ^ (2 : ℕ) ≤
        (((Lf : ℝ) - (σ : ℝ) * t) / 2) *
          ‖@vfista_residual_to_optimum
              E _ _ _ f g Lf σ x0 _ _ _ xStar k‖ ^ (2 : ℕ) := by
    -- Then apply the quadratic-completion estimate `(10.57)` to the pre-step energy.
    simpa using
      (vfista_prestep_quadratic_completion_bound
        hproblem hproblem hstrong xStar k)
  -- Compose the raw balance with the completion bound to obtain the completed recursion.
  nlinarith [hbalance, hcomplete]

/-- Helper for Theorem 10.42: squaring the source parameter `t = √κ` recovers the ratio
`L_f / σ`. -/
lemma vfista_t_sq_eq_ratio :
    t ^ (2 : ℕ) = (Lf : ℝ) / (σ : ℝ) := by
  have hκ_nonneg : 0 ≤ κ :=
    condition_number_nonneg (toNNReal Lf) σ
  -- Expand `κ = L_f / σ` after eliminating the outer square root.
  calc
    t ^ (2 : ℕ) = κ := by
      simpa [pow_two] using Real.sq_sqrt hκ_nonneg
    _ = (Lf : ℝ) / (σ : ℝ) := by
      simp [condition_number_eq, PosReal.coe_toNNReal]

/-- Helper for Theorem 10.42: in the nontrivial branch, the source parameter `t = √κ` satisfies
`1 ≤ t`. -/
lemma vfista_t_one_le
    [Nontrivial E]
    (hproblem : IsFastProximalGradientProblem f g XStar FOpt (toNNReal Lf))
    (hstrong : StrongConvexOn Set.univ (σ : ℝ) f) :
    (1 : ℝ) ≤ t := by
  have hσ_le_Lf :
      (σ : ℝ) ≤ (Lf : ℝ) :=
    smoothness_modulus_dominates_strong_convexity_modulus hproblem hstrong
  have hσ_ne : (σ : ℝ) ≠ 0 := (PosReal.coe_pos σ).ne'
  have hfrac_ge_one : (1 : ℝ) ≤ (Lf : ℝ) / (σ : ℝ) := by
    field_simp [hσ_ne]
    nlinarith
  have hκ_ge_one : (1 : ℝ) ≤ κ := by
    rw [condition_number_eq, PosReal.coe_toNNReal]
    exact hfrac_ge_one
  -- Apply the monotonicity of `Real.sqrt` on `[1, ∞)`.
  change (1 : ℝ) ≤ Real.sqrt κ
  exact Real.one_le_sqrt.mpr hκ_ge_one

/-- Helper for Theorem 10.42: once `x^0` is finite-valued for `g`, every V-FISTA iterate stays in
`effective_domain g`. -/
lemma vfista_iterate_mem_effective_domain_of_initial
    [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (hx0 : x0 ∈ effective_domain g) :
    ∀ n : ℕ, xv n ∈ effective_domain g := by
  intro n
  cases n with
  | zero =>
      -- The base iterate is exactly `x0`.
      simpa using hx0
  | succ k =>
      -- Every successor iterate is a prox-gradient step, hence feasible.
      exact vfista_iterate_succ_mem_effective_domain hproblem k

/-- Helper for Theorem 10.42: the completed real Lyapunov energy contracts by the source factor
`1 - 1 / t` at each feasible V-FISTA step. -/
lemma vfista_real_lyapunov_energy_step
    [Nontrivial E]
    [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (hproblem : IsFastProximalGradientProblem f g XStar FOpt (toNNReal Lf))
    (hstrong : StrongConvexOn Set.univ (σ : ℝ) f)
    (hxStar : xStar ∈ XStar)
    (k : ℕ) (hxk : xv k ∈ effective_domain g) :
    let vR : ℕ → ℝ := fun n ↦ (F (xv n)).toReal - FOpt
    let ER : ℕ → ℝ := fun n ↦
      vR n +
        ((σ : ℝ) / 2) *
          ‖@vfista_residual_to_optimum
              E _ _ _ f g Lf σ x0 _ _ _ xStar n‖ ^ (2 : ℕ)
    ER (k + 1) ≤ (1 - 1 / t) * ER k := by
  let vR : ℕ → ℝ := fun n ↦ (F (xv n)).toReal - FOpt
  let ER : ℕ → ℝ := fun n ↦
    vR n +
      ((σ : ℝ) / 2) *
        ‖@vfista_residual_to_optimum
            E _ _ _ f g Lf σ x0 _ _ _ xStar n‖ ^ (2 : ℕ)
  have hcompleted :
      t ^ (2 : ℕ) * vR (k + 1) +
          ((Lf : ℝ) / 2) *
            ‖@vfista_residual_to_optimum
                E _ _ _ f g Lf σ x0 _ _ _ xStar (k + 1)‖ ^ (2 : ℕ) ≤
        t * (t - 1) * vR k +
          (((Lf : ℝ) - (σ : ℝ) * t) / 2) *
            ‖@vfista_residual_to_optimum
                E _ _ _ f g Lf σ x0 _ _ _ xStar k‖ ^ (2 : ℕ) := by
    -- Start from the completed Lyapunov recursion `(10.57)` proved above.
    simpa [vR] using
      (vfista_lyapunov_completed_real
        hproblem hproblem hstrong hxStar k hxk)
  have ht_one_le : (1 : ℝ) ≤ t :=
    vfista_t_one_le hproblem hstrong
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht_one_le
  have hσ_ne : (σ : ℝ) ≠ 0 := (PosReal.coe_pos σ).ne'
  have hLf_eq :
      (Lf : ℝ) = (σ : ℝ) * t ^ (2 : ℕ) := by
    rw [vfista_t_sq_eq_ratio (Lf := Lf) (σ := σ)]
    field_simp [hσ_ne]
  have hmix :
      (Lf : ℝ) - (σ : ℝ) * t =
        (σ : ℝ) * t * (t - 1) := by
    rw [hLf_eq]
    ring
  have hER_succ :
      t ^ (2 : ℕ) * ER (k + 1) =
        t ^ (2 : ℕ) * vR (k + 1) +
          ((Lf : ℝ) / 2) *
            ‖@vfista_residual_to_optimum
                E _ _ _ f g Lf σ x0 _ _ _ xStar (k + 1)‖ ^ (2 : ℕ) := by
    have hcoef :
        t ^ (2 : ℕ) * ((σ : ℝ) / 2) = (Lf : ℝ) / 2 := by
      rw [hLf_eq]
      ring
    calc
      t ^ (2 : ℕ) * ER (k + 1) =
          t ^ (2 : ℕ) * vR (k + 1) +
            (t ^ (2 : ℕ) * ((σ : ℝ) / 2)) *
              ‖@vfista_residual_to_optimum
                  E _ _ _ f g Lf σ x0 _ _ _ xStar (k + 1)‖ ^ (2 : ℕ) := by
        dsimp [ER]
        ring
      _ = t ^ (2 : ℕ) * vR (k + 1) +
            ((Lf : ℝ) / 2) *
              ‖@vfista_residual_to_optimum
                  E _ _ _ f g Lf σ x0 _ _ _ xStar (k + 1)‖ ^ (2 : ℕ) := by
        rw [hcoef]
  have hER_k :
      t ^ (2 : ℕ) * ((1 - 1 / t) * ER k) =
        t * (t - 1) * vR k +
          (((Lf : ℝ) - (σ : ℝ) * t) / 2) *
            ‖@vfista_residual_to_optimum
                E _ _ _ f g Lf σ x0 _ _ _ xStar k‖ ^ (2 : ℕ) := by
    have hcoef_gap :
        t ^ (2 : ℕ) * (1 - 1 / t) = t * (t - 1) :=
      vfista_scaled_objective_gap_coefficient hproblem hstrong
    have hcoef_res :
        t ^ (2 : ℕ) * ((1 - 1 / t) * ((σ : ℝ) / 2)) =
          (((Lf : ℝ) - (σ : ℝ) * t) / 2) := by
      calc
        t ^ (2 : ℕ) * ((1 - 1 / t) * ((σ : ℝ) / 2)) =
            (t ^ (2 : ℕ) * (1 - 1 / t)) * ((σ : ℝ) / 2) := by
          ring
        _ = (((Lf : ℝ) - (σ : ℝ) * t) / 2) := by
          rw [hcoef_gap]
          nlinarith [hmix]
    calc
      t ^ (2 : ℕ) * ((1 - 1 / t) * ER k) =
          (t ^ (2 : ℕ) * (1 - 1 / t)) * vR k +
            (t ^ (2 : ℕ) * ((1 - 1 / t) * ((σ : ℝ) / 2))) *
              ‖@vfista_residual_to_optimum
                  E _ _ _ f g Lf σ x0 _ _ _ xStar k‖ ^ (2 : ℕ) := by
        dsimp [ER]
        ring
      _ = t * (t - 1) * vR k +
            (((Lf : ℝ) - (σ : ℝ) * t) / 2) *
              ‖@vfista_residual_to_optimum
                  E _ _ _ f g Lf σ x0 _ _ _ xStar k‖ ^ (2 : ℕ) := by
        rw [hcoef_gap, hcoef_res]
  have hscaled :
      t ^ (2 : ℕ) * ER (k + 1) ≤
        t ^ (2 : ℕ) * ((1 - 1 / t) * ER k) := by
    -- Rewrite both sides into the completed Lyapunov recursion and reuse that inequality.
    rw [hER_succ, hER_k]
    exact hcompleted
  have ht_sq_pos : 0 < t ^ (2 : ℕ) := by
    positivity
  -- Cancel the positive factor `t²` to recover the one-step contraction.
  exact le_of_mul_le_mul_left hscaled ht_sq_pos

/-- Helper for Theorem 10.42: iterating the one-step Lyapunov contraction gives the geometric
bound on the completed real energy. -/
lemma vfista_real_lyapunov_energy_le_geometric
    [Nontrivial E]
    [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (hproblem : IsFastProximalGradientProblem f g XStar FOpt (toNNReal Lf))
    (hstrong : StrongConvexOn Set.univ (σ : ℝ) f)
    (hx0 : x0 ∈ effective_domain g)
    (hxStar : xStar ∈ XStar) :
    let vR : ℕ → ℝ := fun n ↦ (F (xv n)).toReal - FOpt
    let ER : ℕ → ℝ := fun n ↦
      vR n +
        ((σ : ℝ) / 2) *
          ‖@vfista_residual_to_optimum
              E _ _ _ f g Lf σ x0 _ _ _ xStar n‖ ^ (2 : ℕ)
    ∀ k : ℕ, ER k ≤ (1 - 1 / t) ^ k * ER 0 := by
  let vR : ℕ → ℝ := fun n ↦ (F (xv n)).toReal - FOpt
  let ER : ℕ → ℝ := fun n ↦
    vR n +
      ((σ : ℝ) / 2) *
        ‖@vfista_residual_to_optimum
            E _ _ _ f g Lf σ x0 _ _ _ xStar n‖ ^ (2 : ℕ)
  have ht_one_le : (1 : ℝ) ≤ t :=
    vfista_t_one_le hproblem hstrong
  have hcoeff_nonneg : 0 ≤ 1 - 1 / t := by
    have hrecip_le_one : 1 / t ≤ (1 : ℝ) := by
      simpa using one_div_le_one_div_of_le zero_lt_one ht_one_le
    linarith
  have hgeom : ∀ k : ℕ, ER k ≤ (1 - 1 / t) ^ k * ER 0 := by
    intro k
    induction k with
    | zero =>
        -- The base energy is bounded by itself.
        simp [ER]
    | succ k ih =>
        have hxk : xv k ∈ effective_domain g :=
          vfista_iterate_mem_effective_domain_of_initial (hproblem := hproblem) hx0 k
        have hstep :
            ER (k + 1) ≤ (1 - 1 / t) * ER k := by
          -- Apply the one-step contraction at the feasible iterate `x^k`.
          simpa [ER, vR] using
            (vfista_real_lyapunov_energy_step
              hproblem hproblem hstrong hxStar k hxk)
        calc
          ER (k + 1) ≤ (1 - 1 / t) * ER k := hstep
          _ ≤ (1 - 1 / t) * ((1 - 1 / t) ^ k * ER 0) := by
            exact mul_le_mul_of_nonneg_left ih hcoeff_nonneg
          _ = (1 - 1 / t) ^ (k + 1) * ER 0 := by
            rw [pow_succ]
            ac_rfl
  simpa [vR, ER] using hgeom

omit [InnerProductSpace ℝ E] [ProperSpace E] in
/-- Helper for Theorem 10.42: the initial completed real Lyapunov energy is exactly the theorem
surface term after coercion back to `EReal`. -/
lemma vfista_initial_energy_surface_bridge
    [IsProperExtendedRealFunction g]
    (hx0 : x0 ∈ effective_domain g) :
    (((((F x0).toReal - FOpt) + ((σ : ℝ) / 2) * ‖x0 - xStar‖ ^ (2 : ℕ) : ℝ)) : EReal) =
      (F x0 - (FOpt : EReal)) +
        ((((σ : ℝ) / 2) * ‖x0 - xStar‖ ^ (2 : ℕ) : ℝ) : EReal) := by
  -- Rewrite the finite initial objective gap before reattaching the quadratic term.
  rw [EReal.coe_add,
    vfista_objective_gap_eq_coe_sub_optimal_value_of_mem_effective_domain (x := x0) hx0]

/-- Helper for Theorem 10.42: in the degenerate case `t = 1`, every positive-index V-FISTA
iterate already attains the optimal objective value. -/
lemma vfista_positive_iterate_eq_optimal_value_of_t_eq_one
    [Nontrivial E]
    [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (hproblem : IsFastProximalGradientProblem f g XStar FOpt (toNNReal Lf))
    (hstrong : StrongConvexOn Set.univ (σ : ℝ) f)
    (ht : t = 1) (hxStar : xStar ∈ XStar)
    (n : ℕ) :
    F (xv (n + 1)) = (FOpt : EReal) := by
  have hxStar_eff : xStar ∈ effective_domain g :=
    vfista_optimal_point_mem_effective_domain hproblem hxStar
  have hxsucc_eff : xv (n + 1) ∈ effective_domain g :=
    vfista_iterate_succ_mem_effective_domain hproblem n
  have hprox0 :
      ((Lf : ℝ) / 2) * ‖xStar - xv (n + 1)‖ ^ (2 : ℕ) -
          (((Lf : ℝ) - (σ : ℝ)) / 2) * ‖xStar - yv n‖ ^ (2 : ℕ) ≤
        (F xStar).toReal - (F (xv (n + 1))).toReal := by
    -- Specialize the real prox-gap inequality at `x*` and the current extrapolated point `y^n`.
    simpa [vfista_x_succ] using
      (vfista_prox_gap_real_of_finite_values hproblem hstrong xStar (yv n) hxStar_eff)
  have hxStar_value :
      F xStar = (FOpt : EReal) :=
    vfista_objective_eq_optimal_value_of_mem_optimal_set hproblem hxStar
  have hxStar_toReal : (F xStar).toReal = FOpt := by
    rw [hxStar_value, EReal.toReal_coe]
  have hratio : (Lf : ℝ) / (σ : ℝ) = 1 := by
    rw [← vfista_t_sq_eq_ratio (Lf := Lf) (σ := σ), ht]
    norm_num
  have hLf_eq_sigma : (Lf : ℝ) = (σ : ℝ) := by
    have hσ_ne : (σ : ℝ) ≠ 0 := (PosReal.coe_pos σ).ne'
    field_simp [hσ_ne] at hratio
    linarith
  have hgap_nonneg :
      0 ≤ (F (xv (n + 1))).toReal - FOpt := by
    have hgapE :
        0 ≤ F (xv (n + 1)) - (FOpt : EReal) :=
      vfista_objective_gap_nonneg (hproblem := hproblem) (n + 1)
    rw [← vfista_objective_gap_eq_coe_sub_optimal_value_of_mem_effective_domain
      (x := xv (n + 1)) hxsucc_eff] at hgapE
    exact EReal.coe_nonneg.mp hgapE
  have hprox :
      ((Lf : ℝ) / 2) * ‖xStar - xv (n + 1)‖ ^ (2 : ℕ) ≤
        FOpt - (F (xv (n + 1))).toReal := by
    -- Route correction: isolate the `t = 1` coefficient collapse before comparing the gap and
    -- the nonnegative quadratic term.
    rw [hxStar_toReal] at hprox0
    simpa [hLf_eq_sigma] using hprox0
  have hvalue :
      (F (xv (n + 1))).toReal = FOpt := by
    have hquad_nonneg :
        0 ≤ ((Lf : ℝ) / 2) * ‖xStar - xv (n + 1)‖ ^ (2 : ℕ) := by
      have hLf_half_nonneg : 0 ≤ ((Lf : ℝ) / 2) := by
        nlinarith [PosReal.coe_pos Lf]
      exact mul_nonneg hLf_half_nonneg (by positivity)
    nlinarith
  have hxsucc_obj :
      F (xv (n + 1)) = ((((F (xv (n + 1))).toReal : ℝ)) : EReal) := by
    rw [vfista_objective_eq_real_of_mem_effective_domain (x := xv (n + 1)) hxsucc_eff,
      EReal.toReal_coe]
  -- Convert the finite-value identity back to the theorem surface.
  rw [hxsucc_obj, hvalue]

-- Proof sketch: apply the fundamental prox-gradient inequality at the V-FISTA extrapolated point
-- `y^k`, use strong convexity of `f` to bound the linearization error from below by the quadratic
-- term with modulus `σ`, combine this with the fixed V-FISTA momentum identity
-- `y^(k+1) = x^(k+1) + ((√κ - 1) / (√κ + 1)) (x^(k+1) - x^k)`, and telescope the resulting
-- Lyapunov recursion to obtain the geometric factor `1 - 1 / √κ`.
/-- Theorem 10.42: under Assumption 10.31, if the smooth term `f` is `σ`-strongly convex, then
the V-FISTA iterates satisfy the geometric objective-gap bound
`F(x^k) - F_opt ≤ (1 - 1 / √κ)^k (F(x^0) - F_opt + (σ / 2) ‖x^0 - x*‖²)`, where
`κ = L_f / σ`. -/
theorem vfista_objective_gap_le_geometric
    (hstrong : StrongConvexOn Set.univ (σ : ℝ) f)
    (hxStar : xStar ∈ XStar) (k : ℕ) :
    F (xv k) - (FOpt : EReal) ≤
      (((1 - 1 / Real.sqrt κ) ^ k : ℝ) : EReal) *
        ((F x0 - (FOpt : EReal)) +
          ((((σ : ℝ) / 2) * ‖x0 - xStar‖ ^ (2 : ℕ) : ℝ) : EReal)) := by
  by_cases hsub : Subsingleton E
  · letI : Subsingleton E := hsub
    have hx0_eq : x0 = xStar := Subsingleton.elim _ _
    have hxk_eq : xv k = xStar := Subsingleton.elim _ _
    have hxStar_value :
        F xStar = (FOpt : EReal) :=
      vfista_objective_eq_optimal_value_of_mem_optimal_set hproblem hxStar
    -- In the subsingleton branch every point equals `x*`, so both the initial energy and the
    -- current objective gap vanish.
    rw [hxk_eq, hx0_eq]
    simp [hxStar_value]
  · letI : Nontrivial E := not_subsingleton_iff_nontrivial.mp hsub
    letI : IsProperExtendedRealFunction g := hproblem.g_proper
    letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
    letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
    by_cases hx0 : x0 ∈ effective_domain g
    · let vR : ℕ → ℝ := fun n ↦ (F (xv n)).toReal - FOpt
      let ER : ℕ → ℝ := fun n ↦
        vR n +
          ((σ : ℝ) / 2) *
            ‖@vfista_residual_to_optimum
                E _ _ _ f g Lf σ x0 _ _ _ xStar n‖ ^ (2 : ℕ)
      have hxk : xv k ∈ effective_domain g :=
        vfista_iterate_mem_effective_domain_of_initial (hproblem := hproblem) hx0 k
      have hdrop :
          vR k ≤ ER k := by
        -- Drop the nonnegative residual term from the completed energy.
        have hres_nonneg :
            0 ≤
              ((σ : ℝ) / 2) *
                ‖@vfista_residual_to_optimum
                    E _ _ _ f g Lf σ x0 _ _ _ xStar k‖ ^ (2 : ℕ) := by
          have hσ_half_nonneg : 0 ≤ ((σ : ℝ) / 2) := by
            nlinarith [PosReal.coe_pos σ]
          exact mul_nonneg hσ_half_nonneg (by positivity)
        dsimp [ER, vR]
        linarith
      have hgeomk :
          ER k ≤ (1 - 1 / t) ^ k * ER 0 := by
        -- Specialize the iterated contraction at the target index `k`.
        simpa [ER, vR] using
          (vfista_real_lyapunov_energy_le_geometric
            hproblem hproblem hstrong hx0 hxStar k)
      have hvR_le :
          vR k ≤ (1 - 1 / t) ^ k * ER 0 :=
        le_trans hdrop hgeomk
      have hcast :
          (((vR k : ℝ)) : EReal) ≤
            ((((1 - 1 / t) ^ k * ER 0 : ℝ)) : EReal) :=
        EReal.coe_le_coe_iff.mpr hvR_le
      have hsurface :
          ((((1 - 1 / t) ^ k * ER 0 : ℝ)) : EReal) =
            (((1 - 1 / t) ^ k : ℝ) : EReal) *
              ((F x0 - (FOpt : EReal)) +
                ((((σ : ℝ) / 2) * ‖x0 - xStar‖ ^ (2 : ℕ) : ℝ) : EReal)) := by
        -- Repackage the initial completed energy as the theorem's source-facing right-hand side.
        rw [EReal.coe_mul]
        congr 1
        simpa [ER, vR, vfista_residual_to_optimum] using
          (vfista_initial_energy_surface_bridge (xStar := xStar) hx0)
      -- Rewrite the finite iterate gap into its real representative and close by the geometric
      -- bound on the completed Lyapunov energy.
      rw [← vfista_objective_gap_eq_coe_sub_optimal_value_of_mem_effective_domain
        (x := xv k) hxk]
      exact hsurface ▸ hcast
    · have hg_top : g x0 = ⊤ := by
        by_contra hg_top
        exact hx0 <| mem_effective_domain.mpr <| lt_top_iff_ne_top.mpr hg_top
      have hFx0_top : F x0 = ⊤ := by
        rw [composite_model_objective_apply, Function.toEReal, hg_top]
        simp
      have hinitial_top :
          (F x0 - (FOpt : EReal)) +
              ((((σ : ℝ) / 2) * ‖x0 - xStar‖ ^ (2 : ℕ) : ℝ) : EReal) = ⊤ := by
        -- The infeasible initial point makes the theorem's source term infinite.
        rw [hFx0_top]
        rw [EReal.top_sub_coe]
        rw [EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)]
      cases k with
      | zero =>
          -- At the initial index, the theorem surface already has `F x0 = ⊤` on both sides.
          rw [vfista_x_zero, hFx0_top, pow_zero, EReal.coe_one, one_mul]
          rw [EReal.top_sub_coe]
          rw [EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)]
      | succ n =>
          by_cases ht : t = 1
          · have hxsucc_value :
              F (xv (n + 1)) = (FOpt : EReal) :=
              vfista_positive_iterate_eq_optimal_value_of_t_eq_one
                hproblem hproblem hstrong ht hxStar n
            have hcoeff_zero :
                ((1 - 1 / Real.sqrt κ) ^ (n + 1) : ℝ) = 0 := by
              rw [ht]
              simp
            -- When `t = 1`, the geometric factor is zero at every positive index.
            rw [hxsucc_value]
            rw [hcoeff_zero]
            simp
          · have ht_one_lt : (1 : ℝ) < t :=
              lt_of_le_of_ne (vfista_t_one_le hproblem hstrong) (Ne.symm ht)
            have ht_pos : 0 < t := lt_trans zero_lt_one ht_one_lt
            have hbase_pos : 0 < 1 - 1 / t := by
              have hrecip_lt : 1 / t < (1 : ℝ) := by
                simpa [one_div] using inv_lt_one_of_one_lt₀ ht_one_lt
              linarith
            have hcoeff_pos :
                0 < (1 - 1 / t : ℝ) ^ (n + 1) :=
              pow_pos hbase_pos (n + 1)
            -- For `t > 1`, the geometric coefficient is strictly positive, so multiplying by the
            -- infinite initial energy leaves the right-hand side equal to `⊤`.
            rw [hinitial_top, EReal.coe_mul_top_of_pos hcoeff_pos]
            exact le_top

end Problem

end

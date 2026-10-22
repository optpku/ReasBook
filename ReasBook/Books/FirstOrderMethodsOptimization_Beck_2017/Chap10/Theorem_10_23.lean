/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_10
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_15
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Remark_10_19

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/- Theorem 10.23 is `source-facing` in the convex proximal-gradient API.

Domain sampling in the existing Chapter 10 development identifies:
- `IsConvexCompositeSmoothMinimizationProblem` as the owner for Assumption 10.1 together with the
  convexity of `f`;
- `is_proximal_gradient_trajectory` as the owner for the generated sequence `x^k`;
- `hproblem.ConstantOrBacktrackingB2StepsizeRule` as the canonical Chapter 10 bridge/view owner
  for the admissible `L_k = L_f` or B2-backtracking regime from Remark 10.19;
- `hproblem.upper_model_of_constantOrBacktrackingB2Rule` from Remark 10.19 as the derived
  trajectory-level upper-model bridge needed in the Fejér proof;
- `IsFejerMonotoneWithRespectTo` from Chapter 8 as the canonical owner abstraction for the
  theorem's conclusion.

Triage for this file:
- `source-facing`: the Fejer-monotonicity theorem for proximal-gradient iterates;
- `core/canonical`: the convex composite problem owner and the proximal-gradient trajectory owner;
- `bridge/view`: the constant-or-B2 stepsize owner from Remark 10.19 and the Chapter 8 Fejer
  predicate.

Primitive data are therefore the convex composite problem instance, the trajectory, and the
admissible constant-or-B2 stepsize regime. Properness of the ambient space is not primitive here:
it only enters later in the convergence layer when cluster points must be extracted. The auxiliary
rate constant `α` from the sublinear-rate owner is derived bridge data for later rate statements
and does not belong in Theorem 10.23. The pointwise norm inequality against a chosen optimizer is
derived API from the Fejér-monotonicity owner, so the file keeps only the canonical owner-level
theorem. -/

variable {f g : E → EReal} {XStar : Set E} {FOpt : ℝ} {Lf : NNReal}
variable [hproblem : IsConvexCompositeSmoothMinimizationProblem f g XStar FOpt Lf]
variable {x : ℕ → E} {L : ℕ → PosReal}

local notation "F" => composite_model_objective f g

/-- Helper for Theorem 10.23: a proximal membership already yields the effective-domain inclusion
and affine support inequality for the proximal objective, without first packaging the proximal set
as a singleton. -/
private lemma memProxImpliesEffectiveDomainAndInnerSupport
    (f : E → EReal) (hf_proper : IsProperExtendedRealFunction f)
    (hf_convex : is_convex_function f) (x u : E) (hu : u ∈ prox[f] x) :
    u ∈ effective_domain f ∧
      ∀ y ∈ effective_domain f, ((inner ℝ (x - u) (y - u) : ℝ) : EReal) ≤ f y - f u := by
  -- Route correction: keep the support argument at the set-valued proximal level instead of
  -- forcing a singleton operator description that needs stronger ambient hypotheses.
  have hu_eff : u ∈ effective_domain f := mem_effective_domain_of_mem_prox f hf_proper x hu
  refine ⟨hu_eff, ?_⟩
  intro y hy_eff
  by_cases hyu : y = u
  · -- At `y = u`, the support inequality is the trivial `0 ≤ 0`.
    subst y
    have hzero : ((0 : ℝ) : EReal) ≤ f u - f u := by
      have hsupport_add :
          ((0 : ℝ) : EReal) + f u ≤ f u := by
        simp
      exact (EReal.le_sub_iff_add_le (.inl (hf_proper.ne_bot u))
        (.inl (mem_effective_domain.mp hu_eff).ne)).2 hsupport_add
    simpa using hzero
  · set A : ℝ := inner ℝ (x - u) (y - u) - ((f y).toReal - (f u).toReal)
    set B : ℝ := (1 / 2 : ℝ) * ‖y - u‖ ^ (2 : ℕ)
    have hA_le_tB : ∀ {t : ℝ}, 0 < t → t ≤ 1 → A ≤ t * B := by
      intro t ht_pos ht_one
      have ht_mem : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht_pos.le, ht_one⟩
      let z : E := t • y + (1 - t) • u
      have hz_eff : z ∈ effective_domain f :=
        combo_mem_effective_domain_of_is_convex_function hf_convex hy_eff hu_eff ht_mem
      have hy_val :
          f y = (((f y).toReal : ℝ) : EReal) := by
        exact
          (EReal.coe_toReal (mem_effective_domain.mp hy_eff).ne (hf_proper.ne_bot y)).symm
      have hu_min : proximal_objective f x u ≤ proximal_objective f x z := by
        -- Unfold the proximal membership into minimality of the penalized objective.
        rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hu
        exact hu z
      have hu_val :
          f u = (((f u).toReal : ℝ) : EReal) := by
        exact
          (EReal.coe_toReal (mem_effective_domain.mp hu_eff).ne (hf_proper.ne_bot u)).symm
      have hz_val :
          f z = (((f z).toReal : ℝ) : EReal) := by
        exact
          (EReal.coe_toReal (mem_effective_domain.mp hz_eff).ne (hf_proper.ne_bot z)).symm
      have hu_obj_real :
          (f u).toReal + (1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ) ≤
            (f z).toReal + (1 / 2 : ℝ) * ‖z - x‖ ^ (2 : ℕ) := by
        -- Convert proximal minimality from `EReal` to the real line at finite points.
        have hu_min' := hu_min
        rw [proximal_objective_apply, proximal_objective_apply, hu_val, hz_val] at hu_min'
        have hu_min'' :
            ((((f u).toReal + (1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ) : ℝ)) : EReal) ≤
              ((((f z).toReal + (1 / 2 : ℝ) * ‖z - x‖ ^ (2 : ℕ) : ℝ)) : EReal) := by
          simpa [EReal.coe_add] using hu_min'
        exact EReal.coe_le_coe_iff.mp hu_min''
      have hz_convE :
          f z ≤ (t : EReal) * f y + ((1 - t : ℝ) : EReal) * f u := by
        -- Convexity controls the objective along the segment from `u` to `y`.
        simpa [z, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
          (is_convex_function_iff_segment_ineq.mp hf_convex) y hy_eff u hu_eff ht_mem
      have hz_conv :
          (f z).toReal ≤ t * (f y).toReal + (1 - t) * (f u).toReal := by
        have hz_convE' := hz_convE
        rw [hz_val, hy_val, hu_val] at hz_convE'
        have hz_convE'' :
            (((f z).toReal : ℝ) : EReal) ≤
              ((((t * (f y).toReal + (1 - t) * (f u).toReal : ℝ)) : EReal)) := by
          simpa [EReal.coe_add, EReal.coe_mul] using hz_convE'
        exact EReal.coe_le_coe_iff.mp hz_convE''
      have hz_sub : z - u = t • (y - u) := by
        have hz_def : z = u + t • (y - u) := by
          dsimp [z]
          rw [smul_sub]
          module
        calc
          z - u = (u + t • (y - u)) - u := by rw [hz_def]
          _ = t • (y - u) := by abel
      have hinner_smul :
          inner ℝ (u - x) (t • (y - u)) = -t * inner ℝ (x - u) (y - u) := by
        have hinner_base :
            inner ℝ (u - x) (y - u) = -inner ℝ (x - u) (y - u) := by
          have hneg : u - x = -(x - u) := by
            abel
          rw [hneg, inner_neg_left]
        rw [inner_smul_right]
        rw [hinner_base]
        ring
      have hnorm_smul :
          (1 / 2 : ℝ) * ‖t • (y - u)‖ ^ (2 : ℕ) = t ^ (2 : ℕ) * B := by
        dsimp [B]
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht_pos.le]
        ring
      have hz_quad :
          (1 / 2 : ℝ) * ‖z - x‖ ^ (2 : ℕ) =
            (1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ) - t * inner ℝ (x - u) (y - u) +
              t ^ (2 : ℕ) * B := by
        -- The quadratic identity isolates the linear support term plus a `t^2` remainder.
        calc
          (1 / 2 : ℝ) * ‖z - x‖ ^ (2 : ℕ) =
              (1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ) + inner ℝ (u - x) (z - u) +
                (1 / 2 : ℝ) * ‖z - u‖ ^ (2 : ℕ) := quadratic_translate_identity x u z
          _ = (1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ) - t * inner ℝ (x - u) (y - u) +
                t ^ (2 : ℕ) * B := by
            rw [hz_sub, hinner_smul, hnorm_smul]
            ring
      have hstep :
          (f u).toReal + inner ℝ (x - u) (y - u) - (f y).toReal ≤ t * B := by
        nlinarith [hu_obj_real, hz_conv, hz_quad]
      simpa [A, B, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hstep
    have hB_nonneg : 0 ≤ B := by
      dsimp [B]
      positivity
    have hA_nonpos : A ≤ 0 := by
      by_contra hA
      have hA_pos : 0 < A := lt_of_not_ge hA
      let t : ℝ := min 1 (A / (B + 1))
      have ht_pos : 0 < t := by
        dsimp [t]
        refine lt_min (by norm_num) ?_
        have hden_pos : 0 < B + 1 := by
          linarith
        exact div_pos hA_pos hden_pos
      have ht_one : t ≤ 1 := by
        dsimp [t]
        exact min_le_left _ _
      have hAt : A ≤ t * B := hA_le_tB ht_pos ht_one
      have ht_bound : t ≤ A / (B + 1) := by
        dsimp [t]
        exact min_le_right _ _
      have hmul_bound : t * B ≤ A * B / (B + 1) := by
        have := mul_le_mul_of_nonneg_right ht_bound hB_nonneg
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
      have hstrict : A * B / (B + 1) < A := by
        have hden_pos : 0 < B + 1 := by
          linarith
        field_simp [hden_pos.ne']
        nlinarith [hA_pos, hB_nonneg]
      exact (not_lt_of_ge (le_trans hAt hmul_bound)) hstrict
    have hreal :
        inner ℝ (x - u) (y - u) ≤ (f y).toReal - (f u).toReal := by
      dsimp [A] at hA_nonpos
      linarith
    have hsupport_add_real :
        inner ℝ (x - u) (y - u) + (f u).toReal ≤ (f y).toReal := by
      linarith
    have hsupport_addE :
        ((((inner ℝ (x - u) (y - u) + (f u).toReal : ℝ)) : EReal)) ≤
          (((f y).toReal : ℝ) : EReal) := EReal.coe_le_coe hsupport_add_real
    have hu_val :
        f u = (((f u).toReal : ℝ) : EReal) := by
      exact
        (EReal.coe_toReal (mem_effective_domain.mp hu_eff).ne (hf_proper.ne_bot u)).symm
    have hy_val :
        f y = (((f y).toReal : ℝ) : EReal) := by
      exact
        (EReal.coe_toReal (mem_effective_domain.mp hy_eff).ne (hf_proper.ne_bot y)).symm
    have hsupport_add :
        (((inner ℝ (x - u) (y - u) : ℝ)) : EReal) + f u ≤ f y := by
      rw [hu_val, hy_val]
      simpa [EReal.coe_add] using hsupport_addE
    exact (EReal.le_sub_iff_add_le (.inl (hf_proper.ne_bot u))
      (.inl (mem_effective_domain.mp hu_eff).ne)).2 hsupport_add

/-- Helper for Theorem 10.23: descaling the proximal support inequality for `((c : EReal) • g)`
gives the affine support inequality for `g` itself. -/
private lemma memScaledProxImpliesEffectiveDomainAndInnerSupport
    [IsProperExtendedRealFunction g] [Fact (is_convex_function g)]
    (c : PosReal) (x u : E) (hu : u ∈ prox[((c : EReal) • g)] x) :
    u ∈ effective_domain g ∧
      ∀ y ∈ effective_domain g,
        ((inner ℝ ((1 / c : ℝ) • (x - u)) (y - u) : ℝ) : EReal) ≤ g y - g u := by
  let gScaled : E → EReal := ((c : EReal) • g)
  have hgScaled_proper : IsProperExtendedRealFunction gScaled :=
    scaled_function_proper_of_pos g c inferInstance
  have hg_convex : is_convex_function g := Fact.out
  have hgScaled_convex : is_convex_function gScaled :=
    scaled_function_convex_of_pos g c inferInstance hg_convex
  rcases memProxImpliesEffectiveDomainAndInnerSupport
      gScaled hgScaled_proper hgScaled_convex x u hu with
    ⟨hu_eff_scaled, hsupport_scaled⟩
  have hu_eff : u ∈ effective_domain g :=
    (mem_effective_domain_scaled_function_iff g c inferInstance u).mp hu_eff_scaled
  refine ⟨hu_eff, ?_⟩
  intro y hy
  have hy_scaled : y ∈ effective_domain gScaled :=
    (mem_effective_domain_scaled_function_iff g c inferInstance y).mpr hy
  have hu_val :
      g u = (((g u).toReal : ℝ) : EReal) := by
    exact
      (EReal.coe_toReal (mem_effective_domain.mp hu_eff).ne
        ((inferInstance : IsProperExtendedRealFunction g).ne_bot u)).symm
  have hy_val :
      g y = (((g y).toReal : ℝ) : EReal) := by
    exact
      (EReal.coe_toReal (mem_effective_domain.mp hy).ne
        ((inferInstance : IsProperExtendedRealFunction g).ne_bot y)).symm
  have hu_scaled_val :
      gScaled u = ((((c : ℝ) * (g u).toReal : ℝ)) : EReal) := by
    have htoReal : (gScaled u).toReal = (c : ℝ) * (g u).toReal := by
      change (((c : EReal) * g u).toReal) = (c : ℝ) * (g u).toReal
      rw [EReal.toReal_mul, EReal.toReal_coe]
    calc
      gScaled u = (((gScaled u).toReal : ℝ) : EReal) := by
        rw [EReal.coe_toReal (mem_effective_domain.mp hu_eff_scaled).ne (hgScaled_proper.ne_bot u)]
      _ = ((((c : ℝ) * (g u).toReal : ℝ)) : EReal) := by
        exact congrArg (fun r : ℝ ↦ ((r : ℝ) : EReal)) htoReal
  have hy_scaled_val :
      gScaled y = ((((c : ℝ) * (g y).toReal : ℝ)) : EReal) := by
    have htoReal : (gScaled y).toReal = (c : ℝ) * (g y).toReal := by
      change (((c : EReal) * g y).toReal) = (c : ℝ) * (g y).toReal
      rw [EReal.toReal_mul, EReal.toReal_coe]
    calc
      gScaled y = (((gScaled y).toReal : ℝ) : EReal) := by
        rw [EReal.coe_toReal (mem_effective_domain.mp hy_scaled).ne (hgScaled_proper.ne_bot y)]
      _ = ((((c : ℝ) * (g y).toReal : ℝ)) : EReal) := by
        exact congrArg (fun r : ℝ ↦ ((r : ℝ) : EReal)) htoReal
  have hsupport_real :
      inner ℝ (x - u) (y - u) ≤ (c : ℝ) * ((g y).toReal - (g u).toReal) := by
    have hsupportE := hsupport_scaled y hy_scaled
    rw [hu_scaled_val, hy_scaled_val] at hsupportE
    have hsupportE' :
        (((inner ℝ (x - u) (y - u) : ℝ)) : EReal) ≤
          ((((c : ℝ) * ((g y).toReal - (g u).toReal) : ℝ)) : EReal) := by
      simpa [EReal.coe_sub, mul_sub_left_distrib] using hsupportE
    exact EReal.coe_le_coe_iff.mp hsupportE'
  have hsupport_div :
      inner ℝ ((1 / c : ℝ) • (x - u)) (y - u) ≤ (g y).toReal - (g u).toReal := by
    have hscaled :
        (1 / c : ℝ) * inner ℝ (x - u) (y - u) ≤
          (1 / c : ℝ) * ((c : ℝ) * ((g y).toReal - (g u).toReal)) := by
      exact
        mul_le_mul_of_nonneg_left hsupport_real
          (by
            simpa [one_div] using
              inv_nonneg.mpr (show 0 ≤ (c : ℝ) by exact le_of_lt c.2))
    have hcancel :
        (1 / c : ℝ) * ((c : ℝ) * ((g y).toReal - (g u).toReal)) =
          (g y).toReal - (g u).toReal := by
      field_simp [show (c : ℝ) ≠ 0 by exact_mod_cast c.2.ne']
    calc
      inner ℝ ((1 / c : ℝ) • (x - u)) (y - u)
          = (1 / c : ℝ) * inner ℝ (x - u) (y - u) := by
            simpa using inner_smul_left (x - u) (y - u) (1 / c : ℝ)
      _ ≤ (1 / c : ℝ) * ((c : ℝ) * ((g y).toReal - (g u).toReal)) := hscaled
      _ = (g y).toReal - (g u).toReal := hcancel
  have hsupport_realE :
      (((inner ℝ ((1 / c : ℝ) • (x - u)) (y - u) : ℝ)) : EReal) ≤
        ((((g y).toReal - (g u).toReal : ℝ)) : EReal) := by
    exact_mod_cast hsupport_div
  rw [hy_val, hu_val]
  simpa [EReal.coe_sub] using hsupport_realE

/-- Helper for Theorem 10.23: every optimizer has finite nonsmooth value, so it belongs to
`effective_domain g`. -/
private lemma optimalPointMemEffectiveDomainG
    (hproblem : IsConvexCompositeSmoothMinimizationProblem f g XStar FOpt Lf)
    {xStar : E} (hxStar : xStar ∈ XStar) :
    xStar ∈ effective_domain g := by
  -- The optimal value is finite, so `g xStar = ⊤` would force the composite objective to be `⊤`.
  have hopt :
      F xStar = (FOpt : EReal) :=
    IsConvexCompositeSmoothMinimizationProblem.objective_eq_optimalValue_of_mem_optimalSet
      hproblem hxStar
  have hg_ne_top : g xStar ≠ ⊤ := by
    intro hg_top
    have htop : F xStar = ⊤ := by
      calc
        F xStar = f xStar + g xStar := by rfl
        _ = f xStar + ⊤ := by rw [hg_top]
        _ = ⊤ := EReal.add_top_of_ne_bot (hproblem.f_ne_bot xStar)
    rw [htop] at hopt
    exact EReal.coe_ne_top FOpt hopt.symm
  exact mem_effective_domain.mpr (lt_top_iff_ne_top.mpr hg_ne_top)

/-- Helper for Theorem 10.23: convexity of the smooth term gives the supporting-hyperplane
inequality for the finite-valued restriction `x ↦ (f x).toReal` at a differentiability point. -/
private lemma convexSupportToRealAtBasepoint
    (hproblem : IsConvexCompositeSmoothMinimizationProblem f g XStar FOpt Lf)
    {xBase y : E}
    (hxBase : xBase ∈ effective_domain f)
    (hxDiff : DifferentiableAt ℝ (fun z ↦ (f z).toReal) xBase)
    (hy : y ∈ effective_domain f) :
    (f y).toReal ≥ (f xBase).toReal +
      inner ℝ (∇ (fun z ↦ (f z).toReal) xBase) (y - xBase) := by
  let line : ℝ →ᵃ[ℝ] E := AffineMap.lineMap xBase y
  let φ : ℝ → ℝ := fun t ↦ (f (line t)).toReal
  have hconv :
      ConvexOn ℝ (effective_domain f) (fun z ↦ (f z).toReal) :=
    convexOn_toReal_of_is_convex_function hproblem.f_convex
      (fun z _ ↦ hproblem.f_ne_bot z)
  have hφ_convex :
      ConvexOn ℝ (line ⁻¹' effective_domain f) φ := by
    -- Restrict the convex real-valued model to the segment from `xBase` to `y`.
    simpa [φ, line] using hconv.comp_affineMap line
  have hφ_zero :
      (0 : ℝ) ∈ line ⁻¹' effective_domain f := by
    simpa [line] using hxBase
  have hφ_one :
      (1 : ℝ) ∈ line ⁻¹' effective_domain f := by
    simpa [line] using hy
  have hφ_deriv :
      HasDerivAt φ
        (inner ℝ (∇ (fun z ↦ (f z).toReal) xBase) (y - xBase)) 0 := by
    -- Differentiate the segment restriction and identify the derivative with the gradient pairing.
    have hcomp :
        HasDerivAt φ
          (fderiv ℝ (fun z ↦ (f z).toReal) xBase (y - xBase)) 0 := by
      have hbase :
          HasFDerivAt (fun z ↦ (f z).toReal)
            (fderiv ℝ (fun z ↦ (f z).toReal) xBase) (line 0) := by
        simpa [line] using hxDiff.hasFDerivAt
      have hline : HasDerivAt line (y - xBase) 0 := by
        simpa [line] using
          (show HasDerivAt (AffineMap.lineMap xBase y) (y - xBase) (0 : ℝ) from
            AffineMap.hasDerivAt_lineMap)
      simpa [φ, line] using HasFDerivAt.comp_hasDerivAt 0 hbase hline
    have hgrad :
        fderiv ℝ (fun z ↦ (f z).toReal) xBase (y - xBase) =
          inner ℝ (∇ (fun z ↦ (f z).toReal) xBase) (y - xBase) := by
      simpa using
        (show
            fderiv ℝ (fun z ↦ (f z).toReal) xBase (y - xBase) =
              inner ℝ (∇ (fun z ↦ (f z).toReal) xBase) (y - xBase) from
          HasGradientAt.fderiv_apply hxDiff.hasGradientAt)
    simpa [hgrad] using hcomp
  have hsecant :
      inner ℝ (∇ (fun z ↦ (f z).toReal) xBase) (y - xBase) ≤ slope φ 0 1 := by
    -- Convexity bounds the left derivative by the segment secant slope.
    exact hφ_convex.le_slope_of_hasDerivAt hφ_zero hφ_one zero_lt_one hφ_deriv
  have hsecant' :
      inner ℝ (∇ (fun z ↦ (f z).toReal) xBase) (y - xBase) ≤
        (f y).toReal - (f xBase).toReal := by
    simpa [φ, line, slope] using hsecant
  linarith

/-- Helper for Theorem 10.23: one proximal-gradient step decreases the squared distance to every
optimizer in `XStar`. -/
private lemma proximalGradientStepSqdistLe
    (htraj : is_proximal_gradient_trajectory f g x L)
    (hrule : hproblem.ConstantOrBacktrackingB2StepsizeRule x L htraj)
    {xStar : E} (hxStar : xStar ∈ XStar) (k : ℕ) :
    ‖x (k + 1) - xStar‖ ^ (2 : ℕ) ≤ ‖x k - xStar‖ ^ (2 : ℕ) := by
  let xk := x k
  let xNext := x (k + 1)
  let gradk := ∇ (fun z ↦ (f z).toReal) xk
  let step : E := xk - xNext
  let target : E := xStar - xNext
  have hxk_int :
      xk ∈ interior (effective_domain f) := by
    simpa [xk] using (is_proximal_gradient_trajectory_step htraj k).1
  have hstep :
      xNext ∈ prox[((((1 / L k : PosReal) : EReal) • g))]
        (xk - (1 / (L k : ℝ)) • gradk) := by
    simpa [xk, xNext, gradk, proximal_gradient_step] using
      (is_proximal_gradient_trajectory_step htraj k).2
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  have hxStar_eff_g :
      xStar ∈ effective_domain g :=
    optimalPointMemEffectiveDomainG hproblem hxStar
  have hxStar_eff_f :
      xStar ∈ effective_domain f := by
    exact interior_subset
      (hproblem.g_effective_domain_subset_interior_f_effective_domain hxStar_eff_g)
  rcases memScaledProxImpliesEffectiveDomainAndInnerSupport
      (c := 1 / L k) (x := xk - (1 / (L k : ℝ)) • gradk) (u := xNext) hstep with
    ⟨hxNext_eff_g, hprox_support⟩
  have hxNext_eff_f :
      xNext ∈ effective_domain f := by
    exact interior_subset
      (hproblem.g_effective_domain_subset_interior_f_effective_domain hxNext_eff_g)
  have hxk_val :
      f xk = (((f xk).toReal : ℝ) : EReal) := by
    exact
      (EReal.coe_toReal (mem_effective_domain.mp (interior_subset hxk_int)).ne
        (hproblem.f_ne_bot xk)).symm
  have hxStar_f_val :
      f xStar = (((f xStar).toReal : ℝ) : EReal) := by
    exact
      (EReal.coe_toReal (mem_effective_domain.mp hxStar_eff_f).ne
        (hproblem.f_ne_bot xStar)).symm
  have hxNext_f_val :
      f xNext = (((f xNext).toReal : ℝ) : EReal) := by
    exact
      (EReal.coe_toReal (mem_effective_domain.mp hxNext_eff_f).ne
        (hproblem.f_ne_bot xNext)).symm
  have hxStar_g_val :
      g xStar = (((g xStar).toReal : ℝ) : EReal) := by
    exact
      (EReal.coe_toReal (mem_effective_domain.mp hxStar_eff_g).ne
        ((inferInstance : IsProperExtendedRealFunction g).ne_bot xStar)).symm
  have hxNext_g_val :
      g xNext = (((g xNext).toReal : ℝ) : EReal) := by
    exact
      (EReal.coe_toReal (mem_effective_domain.mp hxNext_eff_g).ne
        ((inferInstance : IsProperExtendedRealFunction g).ne_bot xNext)).symm
  have hxk_diff :
      DifferentiableAt ℝ (fun z ↦ (f z).toReal) xk := by
    exact
      (is_l_smooth_on_iff.mp hproblem.f_toReal_smooth_on_interior_effective_domain).1 _ hxk_int
  have hsupport :
      (f xStar).toReal ≥ (f xk).toReal + inner ℝ gradk (xStar - xk) := by
    -- Convexity of `f` controls the smooth linearization at the current iterate.
    exact convexSupportToRealAtBasepoint
      hproblem
      (xBase := xk) (y := xStar) (interior_subset hxk_int) hxk_diff hxStar_eff_f
  have hupper_real :
      (f xNext).toReal ≤
        (f xk).toReal +
          inner ℝ gradk (xNext - xk) +
          ((L k : ℝ) / 2) * ‖xNext - xk‖ ^ (2 : ℕ) := by
    -- Remark 10.19 supplies the accepted upper model at the realized successor iterate.
    have hupper :=
      hproblem.upper_model_of_constantOrBacktrackingB2Rule htraj hrule k
    rw [hxNext_f_val, hxk_val] at hupper
    exact EReal.coe_le_coe_iff.mp <| by
      simpa [EReal.coe_add, add_assoc, add_left_comm, add_comm] using hupper
  have hopt_real :
      (f xStar).toReal + (g xStar).toReal ≤ (f xNext).toReal + (g xNext).toReal := by
    -- Optimality of `xStar` makes its objective value a lower bound for every iterate value.
    have hoptE :
        F xStar ≤ F xNext := by
      rw [hproblem.objective_eq_optimalValue_of_mem_optimalSet hxStar]
      exact hproblem.optimal_value_isGLB.1 ⟨xNext, rfl⟩
    rw [composite_model_objective_apply, hxStar_f_val, hxStar_g_val,
      composite_model_objective_apply, hxNext_f_val, hxNext_g_val] at hoptE
    simpa [EReal.coe_add] using EReal.coe_le_coe_iff.mp hoptE
  have hgrad_gap :
      (g xStar).toReal - (g xNext).toReal + inner ℝ gradk target ≤
        ((L k : ℝ) / 2) * ‖step‖ ^ (2 : ℕ) := by
    -- The optimality gap is controlled by the smooth upper model plus the convex support bound.
    have hgrad_split :
        inner ℝ gradk target =
          inner ℝ gradk (xStar - xk) - inner ℝ gradk (xNext - xk) := by
      dsimp [target, xk, xNext, gradk]
      rw [show xStar - x (k + 1) = (xStar - x k) - (x (k + 1) - x k) by abel]
      rw [inner_sub_right]
    have hstep_norm :
        ‖xNext - xk‖ ^ (2 : ℕ) = ‖step‖ ^ (2 : ℕ) := by
      dsimp [step, xk, xNext]
      rw [norm_sub_rev]
    rw [hgrad_split]
    have hsupport' :
        (f xk).toReal + inner ℝ gradk (xStar - xk) ≤ (f xStar).toReal := by
      linarith
    have hupper' :
        (f xNext).toReal - (((L k : ℝ) / 2) * ‖step‖ ^ (2 : ℕ)) ≤
          (f xk).toReal + inner ℝ gradk (xNext - xk) := by
      have hupper_real' :
          (f xNext).toReal ≤
            (f xk).toReal +
              inner ℝ gradk (xNext - xk) +
              ((L k : ℝ) / 2) * ‖step‖ ^ (2 : ℕ) := by
        rw [← hstep_norm]
        exact hupper_real
      linarith
    nlinarith [hopt_real, hsupport', hupper']
  have hprox_support_real :
      (L k : ℝ) * inner ℝ step target - inner ℝ gradk target ≤
        (g xStar).toReal - (g xNext).toReal := by
    -- Descale the Chapter 6 prox support inequality at the forward point.
    have hsupportE := hprox_support xStar hxStar_eff_g
    rw [hxStar_g_val, hxNext_g_val] at hsupportE
    have hsupport_real0 :
        inner ℝ
            ((1 / (1 / L k : PosReal) : ℝ) •
              ((xk - (1 / (L k : ℝ)) • gradk) - xNext))
            target ≤
          (g xStar).toReal - (g xNext).toReal := by
      exact EReal.coe_le_coe_iff.mp <| by
        simpa [EReal.coe_sub] using hsupportE
    have hsupport_real1 :
        (L k : ℝ) * inner ℝ (xk - xNext) target ≤
          (g xStar).toReal - (g xNext).toReal + inner ℝ gradk target := by
      have hLinv : (1 / (1 / L k : PosReal) : ℝ) = (L k : ℝ) := by
        simp
      rw [hLinv] at hsupport_real0
      rw [show (xk - (1 / (L k : ℝ)) • gradk) - xNext =
          (xk - xNext) - (1 / (L k : ℝ)) • gradk by abel] at hsupport_real0
      rw [smul_sub, inner_sub_left, real_inner_smul_left] at hsupport_real0
      have hL_ne : (L k : ℝ) ≠ 0 := by
        exact ne_of_gt (PosReal.coe_pos (L k))
      have hsmul_id :
          (L k : ℝ) • ((1 / (L k : ℝ)) • gradk) = gradk := by
        have hcoeff : (L k : ℝ) * (1 / (L k : ℝ)) = 1 := by
          field_simp [hL_ne]
        rw [smul_smul, hcoeff, one_smul]
      rw [hsmul_id] at hsupport_real0
      have hcancel :
          (L k : ℝ) * ((1 / (L k : ℝ)) * inner ℝ gradk target) = inner ℝ gradk target := by
        field_simp [hL_ne]
      nlinarith [hsupport_real0]
    have hL_ne : (L k : ℝ) ≠ 0 := by
      exact ne_of_gt (PosReal.coe_pos (L k))
    have hcancel :
        (L k : ℝ) * ((1 / (L k : ℝ)) * inner ℝ gradk target) = inner ℝ gradk target := by
      field_simp [hL_ne]
    calc
      (L k : ℝ) * inner ℝ step target - inner ℝ gradk target =
          (L k : ℝ) *
              (inner ℝ (xk - xNext) target - (1 / (L k : ℝ)) * inner ℝ gradk target) := by
                dsimp [step]
                rw [mul_sub]
                rw [hcancel]
      _ ≤ (g xStar).toReal - (g xNext).toReal := by
            nlinarith [hsupport_real1]
  have hinner_bound :
      inner ℝ step target ≤ (1 / 2 : ℝ) * ‖step‖ ^ (2 : ℕ) := by
    have hscaled :
        (L k : ℝ) * inner ℝ step target ≤ ((L k : ℝ) / 2) * ‖step‖ ^ (2 : ℕ) := by
      nlinarith [hprox_support_real, hgrad_gap]
    nlinarith [show 0 < (L k : ℝ) from PosReal.coe_pos (L k)]
  have hsq_aux :
      0 ≤ ‖step‖ ^ (2 : ℕ) - 2 * inner ℝ step target := by
    nlinarith
  have hnorm_id :
      ‖step - target‖ ^ (2 : ℕ) =
        ‖step‖ ^ (2 : ℕ) - 2 * inner ℝ step target + ‖target‖ ^ (2 : ℕ) := by
    simpa [pow_two, two_mul, mul_comm, mul_left_comm, mul_assoc] using
      (norm_sub_sq_real step target)
  have hsq :
      ‖target‖ ^ (2 : ℕ) ≤ ‖step - target‖ ^ (2 : ℕ) := by
    rw [hnorm_id]
    nlinarith
  have hsq' :
      ‖xStar - xNext‖ ^ (2 : ℕ) ≤ ‖xk - xStar‖ ^ (2 : ℕ) := by
    simpa [step, target, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsq
  simpa [xNext, xk, norm_sub_rev] using hsq'

-- Proof sketch: apply the fundamental prox-gradient inequality at `x = xStar`, `y = x^k`, and
-- `L = L_k`. Use `hproblem.upper_model_of_constantOrBacktrackingB2Rule` to obtain the local
-- upper-model inequality along the realized trajectory, use convexity of `f` to make the
-- linearization error nonnegative, and use optimality of `xStar` to make
-- `F(xStar) - F(x^(k+1)) ≤ 0`. Rearranging gives the one-step Fejér inequality, and quantifying
-- over all `xStar ∈ XStar` yields the Chapter 8 owner predicate.
/-- Theorem 10.23: under Assumption 10.1, if `f` is convex and `x^k` is generated by the proximal
gradient method with either the exact `L_f` rule or backtracking procedure B2, then the trajectory
is Fejér monotone with respect to the optimal set `XStar = X^*`. -/
theorem proximal_gradient_fejer_monotonicity
    (htraj : is_proximal_gradient_trajectory f g x L)
    (hrule : hproblem.ConstantOrBacktrackingB2StepsizeRule x L htraj) :
    IsFejerMonotoneWithRespectTo x XStar := by
  intro xStar hxStar k
  -- First prove the one-step squared-distance drop against the chosen optimizer.
  have hsq :
      ‖x (k + 1) - xStar‖ ^ (2 : ℕ) ≤ ‖x k - xStar‖ ^ (2 : ℕ) :=
    proximalGradientStepSqdistLe (f := f) (g := g) (XStar := XStar) (FOpt := FOpt)
      (Lf := Lf) htraj hrule hxStar k
  have hnorm :
      ‖x (k + 1) - xStar‖ ≤ ‖x k - xStar‖ := by
    rw [sq_le_sq, abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] at hsq
    exact hsq
  simpa [dist_eq_norm] using hnorm

end

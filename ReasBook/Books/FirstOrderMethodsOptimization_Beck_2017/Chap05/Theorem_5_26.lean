/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.FunctionToEReal
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_4
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_7_1
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_4
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_3
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_30
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Proposition_4_22
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_12
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_15
import FirstOrderMethodsOptimization_Beck_2017.Chap05.ConjugateFunctionStrongDual
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Definition_5_1
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Definition_5_16
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Lemma_5_20
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Lemma_5_7
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Theorem_5_24
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Topology.Instances.EReal.Lemmas

universe u

noncomputable section

open scoped Topology

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- Helper for Theorem 5.26 direct proof repair: a strongly convex extended-real-valued function
is convex in the Chapter 2 source-facing sense. -/
private lemma isConvexFunction_of_isStronglyConvex
    {f : E → EReal} {σ : ℝ} (hf : is_strongly_convex_function f σ) :
    is_convex_function f := by
  -- The real-valued strong-convex owner immediately implies convexity of the same restriction.
  refine (is_convex_function_iff_convexOn_toReal (f := f) (fun x _ ↦ hf.ne_bot x)).2 ?_
  have hstrict :
      StrictConvexOn ℝ (effective_domain f) (fun x ↦ (f x).toReal) :=
    (strongConvexOn_toReal_of_is_strongly_convex_function hf).strictConvexOn hf.sigma_pos
  exact hstrict.convexOn

omit [FiniteDimensional ℝ E] in
/-- Helper for Theorem 5.26 direct proof repair: one subgradient witness for a strongly convex
function yields the quadratic lower support bound needed for coercivity. -/
private lemma strongConvexSubgradientLowerBound
    {f : E → EReal} {σ : ℝ} (hσ : 0 < σ) (h_ne_bot : ∀ z, f z ≠ ⊥)
    (hstrong : StrongConvexOn (effective_domain f) σ (fun z ↦ (f z).toReal)) :
    ∀ x : E, ∀ g ∈ ∂ f(x), ∀ y ∈ effective_domain f,
      f y ≥ f x + ((g (y - x) + (σ / 2) * ‖y - x‖ ^ (2 : ℕ) : ℝ) : EReal) := by
  -- Follow the standard strong-convexity support estimate and separate the diagonal case first.
  intro x g hg y hy
  have hx : x ∈ effective_domain f := (mem_subdifferential.mp hg).1
  by_cases hxy : x = y
  · subst y
    rw [ge_iff_le]
    have hfx :
        f x = (((f x).toReal : ℝ) : EReal) := by
      exact (EReal.coe_toReal (ne_of_lt hx) (h_ne_bot x)).symm
    rw [hfx]
    simp
  · let fx : ℝ := (f x).toReal
    let fy : ℝ := (f y).toReal
    let q : ℝ := (σ / 2) * ‖x - y‖ ^ (2 : ℕ)
    have hq_pos : 0 < q := by
      dsimp [q]
      have hnorm_pos : 0 < ‖x - y‖ := by
        refine norm_pos_iff.mpr ?_
        exact sub_ne_zero.mpr hxy
      positivity
    have hfx :
        f x = ((fx : ℝ) : EReal) := by
      exact (EReal.coe_toReal (ne_of_lt hx) (h_ne_bot x)).symm
    have hfy :
        f y = ((fy : ℝ) : EReal) := by
      exact (EReal.coe_toReal (ne_of_lt hy) (h_ne_bot y)).symm
    have hsub_base :
        g (y - x) ≤ fy - fx :=
      subgradient_eval_le_toReal_sub f x y (fun z _ ↦ h_ne_bot z) hx hy hg
    have hquad_real :
        g (y - x) + q ≤ fy - fx := by
      by_contra hfail
      have hfail' : fy - fx < g (y - x) + q := by
        linarith
      let δ : ℝ := g (y - x) + q - (fy - fx)
      have hδ_pos : 0 < δ := by
        dsimp [δ]
        linarith
      let t : ℝ := min (1 / 2 : ℝ) (δ / (2 * q))
      have ht_pos : 0 < t := by
        dsimp [t]
        refine lt_min ?_ ?_
        · norm_num
        · positivity
      have ht_nonneg : 0 ≤ t := ht_pos.le
      have ht_le_half : t ≤ (1 / 2 : ℝ) := by
        dsimp [t]
        exact min_le_left _ _
      have h_one_sub_nonneg : 0 ≤ 1 - t := by
        exact sub_nonneg.mpr <| le_trans ht_le_half (by norm_num)
      let z : E := (1 - t) • x + t • y
      have hz_mem : z ∈ effective_domain f := by
        refine hstrong.1 hx hy h_one_sub_nonneg ht_nonneg ?_
        linarith
      have hz_sub : z - x = t • (y - x) := by
        dsimp [z]
        calc
          ((1 - t) • x + t • y) - x
              = ((1 - t) • x + t • y) + (-1 : ℝ) • x := by
                  simp [sub_eq_add_neg]
          _ = t • (y - x) := by
                  simp [sub_eq_add_neg, smul_add, add_smul, add_left_comm, add_comm]
      have hsub_z :
          t * g (y - x) ≤ (f z).toReal - fx := by
        have hsub :=
          subgradient_eval_le_toReal_sub f x z (fun z' _ ↦ h_ne_bot z') hx hz_mem hg
        rw [hz_sub, map_smul, smul_eq_mul] at hsub
        simpa [fx] using hsub
      have hstrong_z :
          (f z).toReal ≤
            (1 - t) * fx + t * fy - (1 - t) * t * q := by
        dsimp [z, fx, fy, q]
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          hstrong.2 hx hy h_one_sub_nonneg ht_nonneg (by linarith)
      have hscaled :
          t * g (y - x) ≤ t * (fy - fx) - t * (1 - t) * q := by
        linarith
      have hbound :
          g (y - x) ≤ fy - fx - (1 - t) * q := by
        nlinarith
      have ht_le_ratio : t ≤ δ / (2 * q) := by
        dsimp [t]
        exact min_le_right _ _
      have htq_le_halfδ : t * q ≤ δ / 2 := by
        have hmul : t * q ≤ (δ / (2 * q)) * q :=
          mul_le_mul_of_nonneg_right ht_le_ratio hq_pos.le
        calc
          t * q ≤ (δ / (2 * q)) * q := hmul
          _ = δ / 2 := by
            field_simp [hq_pos.ne']
      linarith
    rw [ge_iff_le, hfx, hfy]
    have hsum_real : fx + (g (y - x) + q) ≤ fy := by
      linarith
    have hsum_ereal :
        (((fx + (g (y - x) + q) : ℝ) : EReal)) ≤ ((fy : ℝ) : EReal) :=
      EReal.coe_le_coe hsum_real
    simpa [fx, fy, q, norm_sub_rev, EReal.coe_add, add_assoc] using hsum_ereal

/-- Helper for Theorem 5.26 direct proof repair: a strong-convexity subgradient bound makes every
real sublevel set bounded. -/
  private lemma boundedRealSublevelSets_of_stronglyConvexSubgradient
    {f : E → EReal} {σ : ℝ} (hf : is_strongly_convex_function f σ)
    (x0 : E) (hx0 : x0 ∈ effective_domain f) {g : Module.Dual ℝ E} (hg : g ∈ ∂f(x0)) :
    ∀ a : ℝ, Bornology.IsBounded {x | f x ≤ (a : EReal)} := by
  -- Reuse the quadratic lower support estimate and compare it with a linear bound from the dual.
  intro a
  let gCLM : E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap g
  let c : ℝ := a - (f x0).toReal + ‖gCLM‖ ^ (2 : ℕ) / σ
  let R : ℝ := Real.sqrt (4 * max c 0 / σ)
  have hσ : 0 < σ := hf.sigma_pos
  have hx0_coe : (((f x0).toReal : ℝ) : EReal) = f x0 := by
    exact EReal.coe_toReal (ne_of_lt (mem_effective_domain.mp hx0)) (hf.ne_bot x0)
  have hquad :=
    strongConvexSubgradientLowerBound hσ hf.ne_bot
      (strongConvexOn_toReal_of_is_strongly_convex_function hf)
  have hsubset : {x | f x ≤ (a : EReal)} ⊆ Metric.closedBall x0 R := by
    intro x hxsub
    have hxsub' : f x ≤ (a : EReal) := by
      simpa using hxsub
    have hx : x ∈ effective_domain f := by
      refine mem_effective_domain.mpr ?_
      exact lt_of_le_of_lt hxsub' (by simp)
    have hx_coe : (((f x).toReal : ℝ) : EReal) = f x := by
      exact EReal.coe_toReal (ne_of_lt (mem_effective_domain.mp hx)) (hf.ne_bot x)
    have hbase :
        (f x0).toReal + (g (x - x0) + (σ / 2) * ‖x - x0‖ ^ (2 : ℕ)) ≤ (f x).toReal := by
      have hsupport := hquad x0 g hg x hx
      rw [ge_iff_le, ← hx0_coe, ← hx_coe] at hsupport
      exact_mod_cast hsupport
    have hsub_real : (f x).toReal ≤ a := by
      rw [← hx_coe] at hxsub'
      exact_mod_cast hxsub'
    have hsupport :
        g (x - x0) + (σ / 2) * ‖x - x0‖ ^ (2 : ℕ) ≤ a - (f x0).toReal := by
      linarith
    have hlin_abs : |g (x - x0)| ≤ ‖gCLM‖ * ‖x - x0‖ := by
      simpa [gCLM] using gCLM.le_opNorm (x - x0)
    have hlin_lower : -(‖gCLM‖ * ‖x - x0‖) ≤ g (x - x0) := by
      exact (abs_le.mp hlin_abs).1
    have hyoung :
        ‖gCLM‖ * ‖x - x0‖ ≤
          (σ / 4) * ‖x - x0‖ ^ (2 : ℕ) + ‖gCLM‖ ^ (2 : ℕ) / σ := by
      have htmp :
          2 * ‖x - x0‖ * ‖gCLM‖ ≤
            (σ / 2) * ‖x - x0‖ ^ (2 : ℕ) + (σ / 2)⁻¹ * ‖gCLM‖ ^ (2 : ℕ) :=
        two_mul_le_add_mul_sq (a := ‖x - x0‖) (b := ‖gCLM‖)
          (show 0 < σ / 2 by positivity)
      have htmp' :
          2 * ‖x - x0‖ * ‖gCLM‖ ≤
            (σ / 2) * ‖x - x0‖ ^ (2 : ℕ) + (2 / σ) * ‖gCLM‖ ^ (2 : ℕ) := by
        rwa [show (σ / 2 : ℝ)⁻¹ = 2 / σ by field_simp [hσ.ne']] at htmp
      have hdouble :
          2 * (‖gCLM‖ * ‖x - x0‖) ≤
            2 * ((σ / 4) * ‖x - x0‖ ^ (2 : ℕ) + ‖gCLM‖ ^ (2 : ℕ) / σ) := by
        calc
          2 * (‖gCLM‖ * ‖x - x0‖) = 2 * ‖x - x0‖ * ‖gCLM‖ := by ring
          _ ≤ (σ / 2) * ‖x - x0‖ ^ (2 : ℕ) + (2 / σ) * ‖gCLM‖ ^ (2 : ℕ) := htmp'
          _ = 2 * ((σ / 4) * ‖x - x0‖ ^ (2 : ℕ) + ‖gCLM‖ ^ (2 : ℕ) / σ) := by
            field_simp [hσ.ne']
            ring
      nlinarith [hdouble]
    have hquarter : (σ / 4) * ‖x - x0‖ ^ (2 : ℕ) ≤ c := by
      dsimp [c]
      nlinarith [hsupport, hlin_lower, hyoung]
    have hsq_c : ‖x - x0‖ ^ (2 : ℕ) ≤ 4 * c / σ := by
      have hσ4 : 0 < σ / 4 := by positivity
      have hdiv : ‖x - x0‖ ^ (2 : ℕ) ≤ c / (σ / 4) := by
        refine (le_div_iff₀ hσ4).2 ?_
        simpa [mul_comm, mul_left_comm, mul_assoc] using hquarter
      calc
        ‖x - x0‖ ^ (2 : ℕ) ≤ c / (σ / 4) := hdiv
        _ = 4 * c / σ := by
          field_simp [hσ.ne']
    have hsq : ‖x - x0‖ ^ (2 : ℕ) ≤ 4 * max c 0 / σ := by
      have hc_le : c ≤ max c 0 := le_max_left c 0
      have hbound : 4 * c / σ ≤ 4 * max c 0 / σ := by
        have hmul : (4 / σ) * c ≤ (4 / σ) * max c 0 := by
          gcongr
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
      exact le_trans hsq_c hbound
    have hnorm : ‖x - x0‖ ≤ R := by
      dsimp [R]
      exact Real.le_sqrt_of_sq_le (by simpa using hsq)
    simpa [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev, R] using hnorm
  exact Metric.isBounded_closedBall.subset hsubset

omit [FiniteDimensional ℝ E] in
/-- Helper for Theorem 5.26 direct proof repair: for a convex real-valued function on `Set.univ`,
the Fréchet derivative at a differentiability point is a continuous-dual subgradient. -/
lemma fderiv_mem_subdifferentialAt_of_convexOn_univ
    {f : E → ℝ} (hf_convex : ConvexOn ℝ Set.univ f) {x : E}
    (hdiff : DifferentiableAt ℝ f x) :
    fderiv ℝ f x ∈ subdifferentialAt f x := by
  -- Rewrite the owner-set membership to the real-valued subgradient inequality.
  rw [subdifferentialAt, mem_strongDualSubdifferential, mem_subdifferential,
    is_subgradient_at_coe_iff]
  intro y
  by_cases hxy : x = y
  · -- On the diagonal, the affine support inequality is an equality.
    subst y
    simp
  · let φ : ℝ → ℝ := fun t ↦ f (AffineMap.lineMap x y t)
    have hφ_convex : ConvexOn ℝ Set.univ φ := by
      -- Restrict convexity of `f` to the line through `x` and `y`.
      simpa [φ] using (hf_convex.comp_affineMap (AffineMap.lineMap x y))
    have hφ_deriv :
        HasDerivAt φ (fderiv ℝ f x (y - x)) 0 := by
      -- The derivative along the line is the Fréchet derivative applied to the displacement.
      simpa [φ, AffineMap.lineMap_apply_zero] using
        hdiff.hasFDerivAt.comp_hasDerivAt_of_eq
          0
          AffineMap.hasDerivAt_lineMap
          (AffineMap.lineMap_apply_zero x y).symm
    have hderiv_le_slope :
        fderiv ℝ f x (y - x) ≤ slope φ 0 1 := by
      -- Convexity on the line bounds the secant slope from below by the derivative at `0`.
      simpa [hφ_deriv.deriv] using
        (hφ_convex.deriv_le_slope (x := 0) (y := 1) (by simp) (by simp) zero_lt_one
          hφ_deriv.differentiableAt)
    have hslope :
        slope φ 0 1 = f y - f x := by
      -- Evaluating the line map at `0` and `1` recovers the endpoint values.
      simp [φ, slope_def_field]
    have hsupport : fderiv ℝ f x (y - x) ≤ f y - f x := by
      simpa [hslope] using hderiv_le_slope
    calc
      f x + fderiv ℝ f x (y - x) = fderiv ℝ f x (y - x) + f x := by ring
      _ ≤ f x + (f y - f x) := by
        simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hsupport (f x)
      _ = f y := by ring

/-- Helper for Theorem 5.26 direct proof repair: every affine perturbation
`x ↦ (y x : EReal) - f x` of a proper closed strongly convex function has a unique maximizer. -/
private lemma existsUniqueIsMaxOn_affineMinus_of_proper_closed_strongConvexOn
    (σ : ℝ) (hσ : 0 < σ) (f : E → EReal) (hf_proper : IsProperExtendedRealFunction f)
    (hclosed : LowerSemicontinuous f)
    (hstrong : StrongConvexOn (effective_domain f) σ (fun x ↦ (f x).toReal)) :
    ∀ y : StrongDual ℝ E, ∃! x : E, IsMaxOn (fun z ↦ (y z : EReal) - f z) Set.univ x := by
  have hf_strong : is_strongly_convex_function f σ := by
    -- Repackage the owner-level strong-convexity hypothesis into the bundled Chapter 5 owner.
    refine is_strongly_convex_function_iff_strongConvexOn_toReal.mpr ?_
    exact ⟨hσ, hf_proper.ne_bot, hstrong⟩
  intro y
  let linearPart : E → EReal := Function.toEReal fun x : E ↦ -y x
  let φ : E → EReal := fun x ↦ linearPart x + f x
  have hlinear_ne_bot : ∀ x : E, linearPart x ≠ ⊥ := by
    -- The affine perturbation term is finite everywhere after the canonical `toEReal` lift.
    intro x
    simp [linearPart]
  have hlinear_closed : LowerSemicontinuous linearPart := by
    -- Continuity of the linear functional gives lower semicontinuity after the `toEReal` lift.
    simpa [linearPart] using
      Function.toEReal_lowerSemicontinuous_of_continuous (-y).continuous
  have hlinear_convex : is_convex_function linearPart := by
    -- A linear functional remains convex after negation and the `toEReal` coercion.
    simpa [linearPart] using
      Function.toEReal_isConvexFunction ((-y).convexOn convex_univ)
  have hφ_closed : LowerSemicontinuous φ := by
    -- Addition preserves lower semicontinuity because the affine perturbation is finite
    -- everywhere and the strongly convex term never takes the value `⊥`.
    have hsum_closed : LowerSemicontinuous (linearPart + f) := by
      refine hlinear_closed.add' hclosed ?_
      intro x
      exact EReal.continuousAt_add
        (.inl (EReal.coe_ne_top (-y x)))
        (.inl (hlinear_ne_bot x))
    simpa [φ, Pi.add_apply] using hsum_closed
  have hφ_strong : is_strongly_convex_function φ σ := by
    -- Adding a convex finite affine term preserves the strong-convexity modulus.
    have hsum_strong :
        is_strongly_convex_function (fun x ↦ f x + linearPart x) σ :=
      is_strongly_convex_function_add_of_is_convex_function
        hf_strong hlinear_convex hlinear_ne_bot
    simpa [φ, Pi.add_apply, add_comm] using hsum_strong
  have hφ_proper : IsProperExtendedRealFunction φ := by
    refine ⟨?_, ?_⟩
    · intro x
      simpa [φ, linearPart, Pi.add_apply] using
        (EReal.add_ne_bot_iff.mpr ⟨hlinear_ne_bot x, hf_proper.ne_bot x⟩)
    · rcases hf_proper.effective_domain_nonempty with ⟨x0, hx0⟩
      refine ⟨x0, ?_⟩
      refine mem_effective_domain.mpr ?_
      simpa [φ, linearPart, Pi.add_apply] using
        EReal.add_lt_top (EReal.coe_ne_top (-y x0)) (ne_of_lt (mem_effective_domain.mp hx0))
  have hφ_convex : is_convex_function φ := isConvexFunction_of_isStronglyConvex hφ_strong
  obtain ⟨x0, hx0, hg_nonempty⟩ :=
    exists_subdifferentiable_point_in_effective_domain_of_proper_convex φ hφ_proper hφ_convex
  obtain ⟨g, hg⟩ := hg_nonempty
  have hlevel :
      ∀ a : ℝ, Bornology.IsBounded {x | φ x ≤ (a : EReal)} :=
    boundedRealSublevelSets_of_stronglyConvexSubgradient hφ_strong x0 hx0 hg
  obtain ⟨xStar, hxStar, hxStarMin⟩ :=
    exists_isMinOn_univ_of_bounded_real_sublevelSets φ hφ_proper hφ_closed hlevel
  let ψ : E → EReal := fun z ↦ (y z : EReal) - f z
  have hneg_eq : (fun z ↦ -φ z) = ψ := by
    -- The affine-maximization objective is exactly the negative of the minimization objective.
    funext z
    by_cases hbot : f z = ⊥
    · simp [ψ, φ, linearPart, hbot, sub_eq_add_neg, add_comm]
    · by_cases htop : f z = ⊤
      · simp [ψ, φ, linearPart, htop, sub_eq_add_neg, add_comm]
      · lift f z to ℝ using ⟨htop, hbot⟩ with fz hfz
        dsimp [ψ, φ, linearPart]
        rw [← hfz]
        simp [sub_eq_add_neg, add_comm, EReal.neg_add]
  refine ⟨xStar, ?_, ?_⟩
  · -- Rewrite the unique minimizer of `φ` as the unique maximizer of the negated affine objective.
    have hmax_neg : IsMaxOn (fun z ↦ -φ z) Set.univ xStar :=
      (isMaxOn_univ_neg_iff_isMinOn_univ (φ := φ) (x := xStar)).2 hxStarMin
    simpa [hneg_eq, ψ] using hmax_neg
  · intro x hx
    have hx_neg : IsMaxOn (fun z ↦ -φ z) Set.univ x := by
      simpa [hneg_eq, ψ] using hx
    have hx_min : IsMinOn φ Set.univ x :=
      (isMaxOn_univ_neg_iff_isMinOn_univ (φ := φ) (x := x)).1 hx_neg
    have hstrict :
        StrictConvexOn ℝ (effective_domain φ) (fun z ↦ (φ z).toReal) :=
      (strongConvexOn_toReal_of_is_strongly_convex_function hφ_strong).strictConvexOn hσ
    have hx_zero : (0 : Module.Dual ℝ E) ∈ ∂ φ(x) := by
      exact (isMinOn_univ_iff_zero_mem_subdifferential (f := φ)
        hφ_proper.effective_domain_nonempty).mp hx_min
    have hx_dom : x ∈ effective_domain φ := (mem_subdifferential.mp hx_zero).1
    have hxStarMinReal :
        IsMinOn (fun z ↦ (φ z).toReal) (effective_domain φ) xStar := by
      rw [isMinOn_iff]
      intro z hz
      have hxStar_coe : (((φ xStar).toReal : ℝ) : EReal) = φ xStar := by
        exact
          EReal.coe_toReal (ne_of_lt (mem_effective_domain.mp hxStar)) (hφ_proper.ne_bot xStar)
      have hz_coe : (((φ z).toReal : ℝ) : EReal) = φ z := by
        exact EReal.coe_toReal (ne_of_lt (mem_effective_domain.mp hz)) (hφ_proper.ne_bot z)
      have hmin : φ xStar ≤ φ z := (isMinOn_iff.mp hxStarMin) z (by simp)
      rw [← hxStar_coe, ← hz_coe] at hmin
      exact_mod_cast hmin
    have hxMinReal :
        IsMinOn (fun z ↦ (φ z).toReal) (effective_domain φ) x := by
      rw [isMinOn_iff]
      intro z hz
      have hx_coe : (((φ x).toReal : ℝ) : EReal) = φ x := by
        exact EReal.coe_toReal (ne_of_lt (mem_effective_domain.mp hx_dom)) (hφ_proper.ne_bot x)
      have hz_coe : (((φ z).toReal : ℝ) : EReal) = φ z := by
        exact EReal.coe_toReal (ne_of_lt (mem_effective_domain.mp hz)) (hφ_proper.ne_bot z)
      have hmin : φ x ≤ φ z := (isMinOn_iff.mp hx_min) z (by simp)
      rw [← hx_coe, ← hz_coe] at hmin
      exact_mod_cast hmin
    exact
      (StrictConvexOn.eq_of_isMinOn (x := xStar) (y := x) hstrict
        hxStarMinReal hxMinReal hxStar hx_dom).symm

/-- Helper for Theorem 5.26 direct proof repair: choose the unique maximizer of the affine
perturbation `x ↦ (y x : EReal) - f x`. -/
private noncomputable def affineMinusMaximizer
    (σ : ℝ) (hσ : 0 < σ) (f : E → EReal) (hf_proper : IsProperExtendedRealFunction f)
    (hclosed : LowerSemicontinuous f)
    (hstrong : StrongConvexOn (effective_domain f) σ (fun x ↦ (f x).toReal)) :
    StrongDual ℝ E → E :=
  fun y ↦ Classical.choose <|
    existsUniqueIsMaxOn_affineMinus_of_proper_closed_strongConvexOn
      σ hσ f hf_proper hclosed hstrong y

/-- Helper for Theorem 5.26 direct proof repair: the chosen affine maximizer really attains the
maximum. -/
private lemma affineMinusMaximizer_isMaxOn
    (σ : ℝ) (hσ : 0 < σ) (f : E → EReal) (hf_proper : IsProperExtendedRealFunction f)
    (hclosed : LowerSemicontinuous f)
    (hstrong : StrongConvexOn (effective_domain f) σ (fun x ↦ (f x).toReal))
    (y : StrongDual ℝ E) :
    IsMaxOn (fun z ↦ (y z : EReal) - f z) Set.univ
      (affineMinusMaximizer σ hσ f hf_proper hclosed hstrong y) := by
  -- Unpack the chosen witness from the unique-maximizer existence theorem.
  exact
    (Classical.choose_spec <|
      existsUniqueIsMaxOn_affineMinus_of_proper_closed_strongConvexOn
        σ hσ f hf_proper hclosed hstrong y).1

/-- Helper for Theorem 5.26 direct proof repair: any affine maximizer must equal the chosen
maximizer. -/
private lemma eq_affineMinusMaximizer_of_isMaxOn
    (σ : ℝ) (hσ : 0 < σ) (f : E → EReal) (hf_proper : IsProperExtendedRealFunction f)
    (hclosed : LowerSemicontinuous f)
    (hstrong : StrongConvexOn (effective_domain f) σ (fun x ↦ (f x).toReal))
    {y : StrongDual ℝ E} {x : E}
    (hx : IsMaxOn (fun z ↦ (y z : EReal) - f z) Set.univ x) :
    x = affineMinusMaximizer σ hσ f hf_proper hclosed hstrong y := by
  -- The uniqueness clause of the affine-maximizer theorem identifies all maximizers.
  exact
    (Classical.choose_spec <|
      existsUniqueIsMaxOn_affineMinus_of_proper_closed_strongConvexOn
        σ hσ f hf_proper hclosed hstrong y).2 x hx

/-- Helper for Theorem 5.26 direct proof repair: the chosen affine maximizer realizes the Fenchel
equality and therefore gives a primal subgradient of `f`. -/
private lemma affineMinusMaximizer_mem_subdifferential
    (σ : ℝ) (hσ : 0 < σ) (f : E → EReal) (hf_proper : IsProperExtendedRealFunction f)
    (hclosed : LowerSemicontinuous f)
    (hstrong : StrongConvexOn (effective_domain f) σ (fun x ↦ (f x).toReal))
    (y : StrongDual ℝ E) :
    ((y : StrongDual ℝ E) : Module.Dual ℝ E) ∈
      ∂ f(affineMinusMaximizer σ hσ f hf_proper hclosed hstrong y) := by
  -- Rewrite the chosen argmax as a Fenchel equality, then apply the Chapter 4 subgradient bridge.
  let x := affineMinusMaximizer σ hσ f hf_proper hclosed hstrong y
  have hmax :
      IsMaxOn (fun z ↦ (y z : EReal) - f z) Set.univ x := by
    simpa [x] using affineMinusMaximizer_isMaxOn σ hσ f hf_proper hclosed hstrong y
  have hconj_eq : conjugate_function f y = (y x : EReal) - f x := by
    simpa [x] using (conjugate_function_eq_iff_isMaxOn_pairing_sub_function f x y).2 hmax
  have hpair :
      (y x : EReal) = f x + conjugate_function f y := by
    have hpair' :
        (y x : EReal) = conjugate_function f y + f x :=
      (eq_add_iff_left_eq_sub_of_ne_bot
        (a := conjugate_function f y)
        (b := f x)
        (c := (y x : EReal))
        (conjugate_function_ne_bot_of_proper f hf_proper y)
        (hf_proper.ne_bot x)
        (EReal.coe_ne_top (y x))).2 hconj_eq
    simpa [add_comm] using hpair'
  exact
    (pairing_eq_add_conjugate_iff_mem_subdifferential_of_proper
      f hf_proper x y).mp hpair

/-- Helper for Theorem 5.26 direct proof repair: the affine-maximizer map is `(1 / σ)`-Lipschitz.
-/
private lemma affineMinusMaximizer_lipschitz
    (σ : ℝ) (hσ : 0 < σ) (f : E → EReal) (hf_proper : IsProperExtendedRealFunction f)
    (hclosed : LowerSemicontinuous f)
    (hstrong : StrongConvexOn (effective_domain f) σ (fun x ↦ (f x).toReal)) :
    ∀ y₁ y₂ : StrongDual ℝ E,
      ‖affineMinusMaximizer σ hσ f hf_proper hclosed hstrong y₁ -
          affineMinusMaximizer σ hσ f hf_proper hclosed hstrong y₂‖ ≤
        (1 / σ) * ‖y₁ - y₂‖ := by
  -- Strong monotonicity of `∂f` turns the two maximizer witnesses into a Lipschitz estimate.
  let T : StrongDual ℝ E → E := affineMinusMaximizer σ hσ f hf_proper hclosed hstrong
  have hquad :
      subgradient_quadratic_lower_bound f σ :=
    subgradientQuadraticLowerBound_of_strongConvexOn hσ hf_proper.ne_bot hstrong
  have hmono :
      subdifferential_strong_monotonicity f σ :=
    subdifferentialStrongMonotonicity_of_subgradientQuadraticLowerBound
      hf_proper.ne_bot hquad
  intro y₁ y₂
  have hy₁ :
      ((y₁ : StrongDual ℝ E) : Module.Dual ℝ E) ∈ ∂ f(T y₁) :=
    affineMinusMaximizer_mem_subdifferential σ hσ f hf_proper hclosed hstrong y₁
  have hy₂ :
      ((y₂ : StrongDual ℝ E) : Module.Dual ℝ E) ∈ ∂ f(T y₂) :=
    affineMinusMaximizer_mem_subdifferential σ hσ f hf_proper hclosed hstrong y₂
  have hpairing :
      σ * ‖T y₁ - T y₂‖ ^ (2 : ℕ) ≤ (y₁ - y₂) (T y₁ - T y₂) := by
    simpa [T] using hmono.apply (T y₁) (T y₂) hy₁ hy₂
  have hupper :
      (y₁ - y₂) (T y₁ - T y₂) ≤ ‖y₁ - y₂‖ * ‖T y₁ - T y₂‖ :=
    (le_abs_self _).trans ((y₁ - y₂).le_opNorm (T y₁ - T y₂))
  by_cases hT : T y₁ = T y₂
  · simpa [T, hT] using (show 0 ≤ (1 / σ) * ‖y₁ - y₂‖ by positivity)
  · have hnorm_pos : 0 < ‖T y₁ - T y₂‖ := by
      exact norm_pos_iff.mpr (sub_ne_zero.mpr hT)
    have hmul :
        (σ * ‖T y₁ - T y₂‖) * ‖T y₁ - T y₂‖ ≤
          ‖y₁ - y₂‖ * ‖T y₁ - T y₂‖ := by
      calc
        (σ * ‖T y₁ - T y₂‖) * ‖T y₁ - T y₂‖ =
            σ * ‖T y₁ - T y₂‖ ^ (2 : ℕ) := by
              rw [pow_two]
              ring
        _ ≤ (y₁ - y₂) (T y₁ - T y₂) := hpairing
        _ ≤ ‖y₁ - y₂‖ * ‖T y₁ - T y₂‖ := hupper
    have hlin : σ * ‖T y₁ - T y₂‖ ≤ ‖y₁ - y₂‖ := by
      nlinarith [hmul]
    have hdiv : ‖T y₁ - T y₂‖ ≤ ‖y₁ - y₂‖ / σ := by
      exact (le_div_iff₀ hσ).2 (by simpa [mul_comm] using hlin)
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv

/-- Helper for Theorem 5.26 direct proof repair: if `a + b = 1`, then the weighted sum
`a * A² + b * B²` dominates `a * b * (A + B)²`. -/
private lemma weightedSqNorm_lowerBound
    {a b A B : ℝ} (_ha : 0 ≤ a) (_hb : 0 ≤ b) (hab : a + b = 1) :
    a * A ^ (2 : ℕ) + b * B ^ (2 : ℕ) ≥ a * b * (A + B) ^ (2 : ℕ) := by
  -- The scalar identity `(a * A - b * B)^2 ≥ 0` is exactly the needed weighted estimate.
  have hb_eq : b = 1 - a := by
    linarith
  rw [hb_eq]
  nlinarith [sq_nonneg (a * A - (1 - a) * B)]

/-- Helper for Theorem 5.26 direct proof repair: smoothness of `f` gives a quadratic lower support
estimate for its continuous-dual Fenchel conjugate at every primal basepoint. -/
private lemma conjugateStrongDual_lowerBound_of_smoothBasepoint
    (σ : ℝ) (hσ : 0 < σ) {f : E → ℝ}
    (hf_smooth : is_l_smooth_on f Set.univ (Real.toNNReal (1 / σ)))
    (x : E) (y : StrongDual ℝ E) :
    conjugate_function_strongDual f.toEReal y ≥
      (y x : EReal) - f x +
        ((((σ / 2) * ‖y - fderiv ℝ f x‖ ^ (2 : ℕ) : ℝ)) : EReal) := by
  let v : StrongDual ℝ E := y - fderiv ℝ f x
  by_cases hv : v = 0
  · -- When the dual mismatch vanishes, evaluating the conjugate at `x` already gives the claim.
    rw [conjugate_function_strongDual_apply, conjugate_function_apply]
    simpa [v, hv] using
      (le_sSup (Set.mem_range_self x) :
        (y x : EReal) - f x ≤
          sSup (Set.range fun z : E ↦ (y z : EReal) - f z))
  · have hv_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hv_dual_pos :
        0 < dualNorm ((v : StrongDual ℝ E) : Module.Dual ℝ E) := by
      simpa [dualNorm_coeStrongDual_eq_norm] using hv_pos
    obtain ⟨u, hu_norm, hu_dual⟩ :=
      existsUnitDualNormWitnessOfPos
        (((v : StrongDual ℝ E) : Module.Dual ℝ E))
        hv_dual_pos
    let z : E := x + (σ * ‖v‖) • u
    have hz_sub : z - x = (σ * ‖v‖) • u := by
      simp [z]
    have hs_nonneg : 0 ≤ σ * ‖v‖ := mul_nonneg hσ.le (norm_nonneg _)
    have hnorm_shift : ‖z - x‖ = σ * ‖v‖ := by
      rw [hz_sub, norm_smul, hu_norm, Real.norm_of_nonneg hs_nonneg, mul_one]
    have hdescent :=
      is_l_smooth_on_univ_fderiv_descent hf_smooth x z
    have hdescent' :
        f z ≤
          f x + fderiv ℝ f x ((σ * ‖v‖) • u) +
            (((1 / σ) / 2) * (σ * ‖v‖) ^ (2 : ℕ)) := by
      have hσinv_nonneg : 0 ≤ 1 / σ := by
        positivity
      rw [hz_sub, Real.toNNReal_of_nonneg hσinv_nonneg] at hdescent
      have hnorm_step : ‖(σ * ‖v‖) • u‖ = σ * ‖v‖ := by
        rw [norm_smul, hu_norm, Real.norm_of_nonneg hs_nonneg, mul_one]
      rw [hnorm_step] at hdescent
      simpa using hdescent
    have hvu : v u = ‖v‖ := by
      simpa [dualNorm_coeStrongDual_eq_norm] using hu_dual
    have hv_eval :
        v ((σ * ‖v‖) • u) = σ * ‖v‖ ^ (2 : ℕ) := by
      rw [map_smul, smul_eq_mul, hvu]
      ring
    have hv_expand :
        y ((σ * ‖v‖) • u) - fderiv ℝ f x ((σ * ‖v‖) • u) =
          σ * ‖v‖ ^ (2 : ℕ) := by
      change v ((σ * ‖v‖) • u) = σ * ‖v‖ ^ (2 : ℕ)
      simpa [v, LinearMap.sub_apply] using hv_eval
    have hquad :
        (((1 / σ) / 2) * (σ * ‖v‖) ^ (2 : ℕ)) = (σ / 2) * ‖v‖ ^ (2 : ℕ) := by
      field_simp [hσ.ne']
    have hreal :
        y z - f z ≥ y x - f x + (σ / 2) * ‖v‖ ^ (2 : ℕ) := by
      -- Evaluate the smooth upper model at the norm-attaining step and collect the exact gain.
      rw [show y z = y x + y ((σ * ‖v‖) • u) by simp [z]]
      nlinarith [hdescent', hv_expand, hquad]
    have hz_eval :
        ((y z : EReal) - f z) ≤ conjugate_function_strongDual f.toEReal y := by
      rw [conjugate_function_strongDual_apply, conjugate_function_apply]
      exact le_sSup (Set.mem_range_self z)
    have hreal_ereal :
        ((((y x - f x + (σ / 2) * ‖v‖ ^ (2 : ℕ) : ℝ)) : EReal)) ≤
          ((y z : EReal) - f z) := by
      exact EReal.coe_le_coe hreal
    exact
      le_trans
        (by
          simpa [v, EReal.coe_add, add_assoc, add_left_comm, add_comm, EReal.coe_sub] using
            hreal_ereal)
        hz_eval

omit [FiniteDimensional ℝ E] in
/-- Helper for Theorem 5.26 direct proof repair: every finite conjugate value admits an
`ε`-Fenchel witness from the supremum definition. -/
private lemma approxFenchelWitness_of_memEffectiveDomain_conjugateStrongDual
    {f : E → ℝ} {y : StrongDual ℝ E} {ε : ℝ}
    (hy : y ∈ effective_domain (conjugate_function_strongDual f.toEReal))
    (hε : 0 < ε) :
    ∃ x : E,
      conjugate_function_strongDual f.toEReal y - (ε : EReal) <
        (y x : EReal) - f x := by
  let gy : EReal := conjugate_function_strongDual f.toEReal y
  let s : Set EReal := Set.range fun x : E ↦ (y x : EReal) - f x
  have hf_proper : IsProperExtendedRealFunction f.toEReal := Function.toEReal_isProper f
  have hgy_ne_bot : gy ≠ ⊥ := by
    simpa [gy, conjugate_function_strongDual_apply] using
      conjugate_function_ne_bot f.toEReal hf_proper y
  have hgy_eq : gy = ((((gy.toReal : ℝ)) : EReal)) := by
    exact (EReal.coe_toReal (ne_of_lt hy) hgy_ne_bot).symm
  have hlt :
      gy - (ε : EReal) < sSup s := by
    have hlt_real : gy.toReal - ε < gy.toReal := by
      linarith
    have hlt_coe : (((gy.toReal - ε : ℝ)) : EReal) < gy := by
      rw [hgy_eq]
      exact_mod_cast hlt_real
    have hgy_sup : gy = sSup s := by
      change conjugate_function_strongDual f.toEReal y = sSup s
      rw [conjugate_function_strongDual_apply, conjugate_function_apply]
      apply congrArg sSup
      ext a
      constructor
      · rintro ⟨x, rfl⟩
        refine ⟨x, ?_⟩
        simp [Function.toEReal]
      · rintro ⟨x, rfl⟩
        refine ⟨x, ?_⟩
        simp [Function.toEReal]
    have hlt_gy : gy - (ε : EReal) < gy := by
      rw [hgy_eq, ← EReal.coe_sub]
      have hlt_coe' := hlt_coe
      rw [hgy_eq] at hlt_coe'
      exact hlt_coe'
    exact hgy_sup ▸ hlt_gy
  obtain ⟨a, ha, hlt'⟩ := lt_sSup_iff.mp hlt
  rcases ha with ⟨x, rfl⟩
  refine ⟨x, ?_⟩
  change gy - (ε : EReal) < (y x : EReal) - f x
  exact hlt'

/-- Theorem 5.26 direct proof repair (1): if `f : E → ℝ` is convex and `(1 / σ)`-smooth on
`Set.univ`, then its
Fenchel conjugate on `StrongDual ℝ E` is `σ`-strongly convex on its effective domain. -/
theorem strongConvexOn_toReal_conjugate_function_of_convex_is_l_smooth
    (σ : ℝ) (hσ : 0 < σ) (f : E → ℝ) (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_smooth : is_l_smooth_on f Set.univ (Real.toNNReal (1 / σ))) :
    StrongConvexOn
      (effective_domain (conjugate_function_strongDual f.toEReal))
      σ
      (fun y : StrongDual ℝ E ↦ (conjugate_function_strongDual f.toEReal y).toReal) := by
  let _ := hf_convex
  let g : StrongDual ℝ E → EReal := conjugate_function_strongDual f.toEReal
  have hf_proper : IsProperExtendedRealFunction f.toEReal := Function.toEReal_isProper f
  have hg_convex : is_convex_function g :=
    (conjugateFunctionStrongDual_closedConvex f.toEReal).2
  refine ⟨?_, ?_⟩
  · -- The conjugate effective domain is convex because the continuous-dual conjugate is convex.
    simpa [g] using effective_domain_convex_of_is_convex_function hg_convex
  · intro y₁ hy₁ y₂ hy₂ a b ha hb hab
    let y : StrongDual ℝ E := a • y₁ + b • y₂
    have hy : y ∈ effective_domain g := by
      simpa [g, y] using
        (effective_domain_convex_of_is_convex_function hg_convex) hy₁ hy₂ ha hb hab
    have hg_ne_bot : ∀ z : StrongDual ℝ E, g z ≠ ⊥ := by
      intro z
      simpa [g, conjugate_function_strongDual_apply] using
        conjugate_function_ne_bot f.toEReal hf_proper z
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨x, hxε⟩ :=
      approxFenchelWitness_of_memEffectiveDomain_conjugateStrongDual
        (f := f) hy hε
    let u : StrongDual ℝ E := fderiv ℝ f x
    let q₁ : ℝ := (σ / 2) * ‖y₁ - u‖ ^ (2 : ℕ)
    let q₂ : ℝ := (σ / 2) * ‖y₂ - u‖ ^ (2 : ℕ)
    have hy₁_eq : conjugate_function_strongDual f.toEReal y₁ = ((((g y₁).toReal : ℝ)) : EReal) := by
      exact (EReal.coe_toReal (ne_of_lt hy₁) (hg_ne_bot y₁)).symm
    have hy₂_eq : conjugate_function_strongDual f.toEReal y₂ = ((((g y₂).toReal : ℝ)) : EReal) := by
      exact (EReal.coe_toReal (ne_of_lt hy₂) (hg_ne_bot y₂)).symm
    have hy_eq : conjugate_function_strongDual f.toEReal y = ((((g y).toReal : ℝ)) : EReal) := by
      exact (EReal.coe_toReal (ne_of_lt hy) (hg_ne_bot y)).symm
    have h₁ :
        y₁ x - f x + q₁ ≤ (g y₁).toReal := by
      -- Apply the smooth basepoint lower-support estimate at `x` and convert the finite
      -- `EReal` inequality back to `ℝ`.
      have hlower :=
        conjugateStrongDual_lowerBound_of_smoothBasepoint
          (σ := σ) hσ hf_smooth x y₁
      rw [ge_iff_le, hy₁_eq] at hlower
      exact_mod_cast hlower
    have h₂ :
        y₂ x - f x + q₂ ≤ (g y₂).toReal := by
      -- The same lower-support estimate controls the second endpoint at the same primal point.
      have hlower :=
        conjugateStrongDual_lowerBound_of_smoothBasepoint
          (σ := σ) hσ hf_smooth x y₂
      rw [ge_iff_le, hy₂_eq] at hlower
      exact_mod_cast hlower
    have hxε_real :
        (g y).toReal - ε < y x - f x := by
      -- Unpack the `ε`-Fenchel witness from the conjugate supremum definition.
      rw [hy_eq] at hxε
      exact_mod_cast hxε
    have hweighted :
        y x - f x + (a * q₁ + b * q₂) ≤
          a * (g y₁).toReal + b * (g y₂).toReal := by
      have hmul :
          a * (y₁ x - f x + q₁) + b * (y₂ x - f x + q₂) ≤
            a * (g y₁).toReal + b * (g y₂).toReal := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left h₁ ha)
          (mul_le_mul_of_nonneg_left h₂ hb)
      have hrewrite :
          a * (y₁ x - f x + q₁) + b * (y₂ x - f x + q₂) =
            y x - f x + (a * q₁ + b * q₂) := by
        rw [show y x = a * y₁ x + b * y₂ x by simp [y]]
        have hfx : a * f x + b * f x = f x := by
          calc
            a * f x + b * f x = (a + b) * f x := by ring
            _ = f x := by rw [hab, one_mul]
        nlinarith [hfx]
      rwa [hrewrite] at hmul
    have htri :
        ‖y₁ - y₂‖ ≤ ‖y₁ - u‖ + ‖y₂ - u‖ := by
      -- Compare the endpoint gap to the sum of the two deviations from the same base dual point.
      have hrewrite : y₁ - y₂ = (y₁ - u) - (y₂ - u) := by
        abel
      rw [hrewrite]
      exact norm_sub_le _ _
    have hquadratic :
        (σ / 2) * a * b * ‖y₁ - y₂‖ ^ (2 : ℕ) ≤ a * q₁ + b * q₂ := by
      -- Triangle inequality plus the scalar weighted-square estimate yields the Banach-space
      -- lower bound needed for the strong-convexity gap.
      have hsq_gap :
          ‖y₁ - y₂‖ ^ (2 : ℕ) ≤ (‖y₁ - u‖ + ‖y₂ - u‖) ^ (2 : ℕ) := by
        have hsum_nonneg : 0 ≤ ‖y₁ - u‖ + ‖y₂ - u‖ := by
          positivity
        nlinarith [htri, hsum_nonneg, norm_nonneg (y₁ - y₂)]
      have hsq_weighted :
          a * ‖y₁ - u‖ ^ (2 : ℕ) + b * ‖y₂ - u‖ ^ (2 : ℕ) ≥
            a * b * (‖y₁ - u‖ + ‖y₂ - u‖) ^ (2 : ℕ) :=
        weightedSqNorm_lowerBound ha hb hab
      have hmid :
          a * b * ‖y₁ - y₂‖ ^ (2 : ℕ) ≤
            a * ‖y₁ - u‖ ^ (2 : ℕ) + b * ‖y₂ - u‖ ^ (2 : ℕ) := by
        have hab_nonneg : 0 ≤ a * b := mul_nonneg ha hb
        have hgap_scaled :
            a * b * ‖y₁ - y₂‖ ^ (2 : ℕ) ≤
              a * b * (‖y₁ - u‖ + ‖y₂ - u‖) ^ (2 : ℕ) :=
          mul_le_mul_of_nonneg_left hsq_gap hab_nonneg
        exact le_trans hgap_scaled hsq_weighted
      have hscale :
          (σ / 2) * (a * b * ‖y₁ - y₂‖ ^ (2 : ℕ)) ≤
            (σ / 2) * (a * ‖y₁ - u‖ ^ (2 : ℕ) + b * ‖y₂ - u‖ ^ (2 : ℕ)) := by
        exact mul_le_mul_of_nonneg_left hmid (by positivity)
      simpa [q₁, q₂, mul_add, add_comm, add_left_comm, add_assoc, mul_assoc, mul_left_comm,
        mul_comm] using hscale
    -- Combine the witness inequality with the two endpoint lower-support estimates and the
    -- quadratic deviation bound, then let `ε → 0`.
    have hfinal :
        (g y).toReal ≤
          a * (g y₁).toReal + b * (g y₂).toReal -
            (σ / 2) * a * b * ‖y₁ - y₂‖ ^ (2 : ℕ) + ε := by
      linarith [hxε_real, hweighted, hquadratic]
    simpa [g, y, sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm,
      add_comm] using hfinal

/-- If `f : E → EReal` is proper, closed, and `σ`-strongly convex, then its Fenchel conjugate on
`StrongDual ℝ E` is finite everywhere. -/
theorem conjugate_function_finite_of_proper_closed_strongConvexOn
    (σ : ℝ) (hσ : 0 < σ) (f : E → EReal) (hf_proper : IsProperExtendedRealFunction f)
    (hclosed : LowerSemicontinuous f)
    (hstrong : StrongConvexOn (effective_domain f) σ (fun x ↦ (f x).toReal)) :
    ∀ y : StrongDual ℝ E,
      conjugate_function_strongDual f y ≠ ⊥ ∧ conjugate_function_strongDual f y < ⊤ := by
  -- Route correction: minimize the affine perturbation `x ↦ (- y x : EReal) + f x`, then turn
  -- the minimizer inequality into a pointwise upper bound on the conjugate supremum.
  have hf_strong : is_strongly_convex_function f σ := by
    refine is_strongly_convex_function_iff_strongConvexOn_toReal.mpr ?_
    exact ⟨hσ, hf_proper.ne_bot, hstrong⟩
  intro y
  let linearPart : E → EReal := Function.toEReal fun x : E ↦ -y x
  let φ : E → EReal := fun x ↦ linearPart x + f x
  have hlinear_ne_bot : ∀ x : E, linearPart x ≠ ⊥ := by
    intro x
    simp [linearPart]
  have hlinear_closed : LowerSemicontinuous linearPart := by
    -- The affine perturbation term is continuous after the canonical `toEReal` lift.
    simpa [linearPart] using
      Function.toEReal_lowerSemicontinuous_of_continuous (-y).continuous
  have hlinear_convex : is_convex_function linearPart := by
    -- A linear functional remains convex after negation and the `toEReal` lift.
    simpa [linearPart] using
      Function.toEReal_isConvexFunction ((-y).convexOn convex_univ)
  have hφ_closed : LowerSemicontinuous φ := by
    -- Addition is continuous because the linear perturbation is finite everywhere and `f` never
    -- takes the value `⊥`.
    have hsum_closed : LowerSemicontinuous (linearPart + f) := by
      refine hlinear_closed.add' hclosed ?_
      intro x
      exact EReal.continuousAt_add
        (.inl (EReal.coe_ne_top (-y x)))
        (.inl (hlinear_ne_bot x))
    simpa [φ, Pi.add_apply] using hsum_closed
  have hφ_strong : is_strongly_convex_function φ σ := by
    -- Adding a convex finite affine term preserves the strong-convexity modulus.
    have hsum_strong :
        is_strongly_convex_function (fun x ↦ f x + linearPart x) σ :=
      is_strongly_convex_function_add_of_is_convex_function
        hf_strong hlinear_convex hlinear_ne_bot
    simpa [φ, Pi.add_apply, add_comm] using hsum_strong
  have hφ_proper : IsProperExtendedRealFunction φ := by
    refine ⟨?_, ?_⟩
    · intro x
      simpa [φ, linearPart, Pi.add_apply] using
        (EReal.add_ne_bot_iff.mpr ⟨hlinear_ne_bot x, hf_proper.ne_bot x⟩)
    · rcases hf_proper.effective_domain_nonempty with ⟨x0, hx0⟩
      refine ⟨x0, ?_⟩
      refine mem_effective_domain.mpr ?_
      simpa [φ, linearPart, Pi.add_apply] using
        EReal.add_lt_top (EReal.coe_ne_top (-y x0)) (ne_of_lt (mem_effective_domain.mp hx0))
  have hφ_convex : is_convex_function φ := isConvexFunction_of_isStronglyConvex hφ_strong
  obtain ⟨x0, hx0, hg_nonempty⟩ :=
    exists_subdifferentiable_point_in_effective_domain_of_proper_convex φ hφ_proper hφ_convex
  obtain ⟨g, hg⟩ := hg_nonempty
  have hlevel :
      ∀ a : ℝ, Bornology.IsBounded {x | φ x ≤ (a : EReal)} :=
    boundedRealSublevelSets_of_stronglyConvexSubgradient hφ_strong x0 hx0 hg
  obtain ⟨xStar, hxStar, hxStarMin⟩ :=
    exists_isMinOn_univ_of_bounded_real_sublevelSets φ hφ_proper hφ_closed hlevel
  have hphi_domain_eq :
      effective_domain φ = effective_domain f := by
    ext x
    constructor
    · intro hx
      rw [mem_effective_domain] at hx ⊢
      by_contra hfx
      have hfx_top : f x = ⊤ := le_antisymm le_top (not_lt.mp hfx)
      have hphi_top : φ x = ⊤ := by
        simp [φ, linearPart, hfx_top]
      exact hx.ne hphi_top
    · intro hx
      refine mem_effective_domain.mpr ?_
      rw [mem_effective_domain] at hx
      simpa [φ, linearPart] using
        EReal.add_lt_top (EReal.coe_ne_top (-y x)) (ne_of_lt hx)
  have hxStar_f : xStar ∈ effective_domain f := by
    simpa [hphi_domain_eq] using hxStar
  have hxStar_f_eq : f xStar = (((f xStar).toReal : ℝ) : EReal) := by
    exact
      (EReal.coe_toReal (ne_of_lt (mem_effective_domain.mp hxStar_f))
        (hf_proper.ne_bot xStar)).symm
  have hbound :
      conjugate_function_strongDual f y ≤ (y xStar : EReal) - f xStar := by
    rw [conjugate_function_strongDual_apply, conjugate_function_apply]
    refine sSup_le ?_
    rintro _ ⟨x, rfl⟩
    by_cases hx : x ∈ effective_domain f
    · have hφx : x ∈ effective_domain φ := by
        simpa [hphi_domain_eq] using hx
      have hmin : φ xStar ≤ φ x := (isMinOn_iff.mp hxStarMin) x (by simp)
      have hφxStar_eq : φ xStar = (((φ xStar).toReal : ℝ) : EReal) := by
        exact
          (EReal.coe_toReal (ne_of_lt (mem_effective_domain.mp hxStar))
            (hφ_proper.ne_bot xStar)).symm
      have hφx_eq : φ x = (((φ x).toReal : ℝ) : EReal) := by
        exact
          (EReal.coe_toReal (ne_of_lt (mem_effective_domain.mp hφx))
            (hφ_proper.ne_bot x)).symm
      have hreal : (φ xStar).toReal ≤ (φ x).toReal := by
        rw [hφxStar_eq, hφx_eq] at hmin
        exact_mod_cast hmin
      have hφxStar_toReal : (φ xStar).toReal = (f xStar).toReal - y xStar := by
        -- Expand the finite affine perturbation into a real-valued expression.
        simpa [φ, linearPart, Pi.add_apply, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
          using
            (EReal.toReal_add (EReal.coe_ne_top (-y xStar)) (EReal.coe_ne_bot (-y xStar))
              (ne_of_lt (mem_effective_domain.mp hxStar_f)) (hf_proper.ne_bot xStar))
      have hfx_eq : f x = (((f x).toReal : ℝ) : EReal) := by
        exact
          (EReal.coe_toReal (ne_of_lt (mem_effective_domain.mp hx))
            (hf_proper.ne_bot x)).symm
      have hφx_toReal : (φ x).toReal = (f x).toReal - y x := by
        -- The same finite-value normalization applies at any effective-domain point of `f`.
        simpa [φ, linearPart, Pi.add_apply, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
          using
            (EReal.toReal_add (EReal.coe_ne_top (-y x)) (EReal.coe_ne_bot (-y x))
              (ne_of_lt (mem_effective_domain.mp hx)) (hf_proper.ne_bot x))
      have hpair_real : y x - (f x).toReal ≤ y xStar - (f xStar).toReal := by
        rw [hφxStar_toReal, hφx_toReal] at hreal
        linarith
      have hpair_ereal :
          (((y x - (f x).toReal : ℝ) : EReal)) ≤
            (((y xStar - (f xStar).toReal : ℝ) : EReal)) :=
        EReal.coe_le_coe hpair_real
      have hpair_ereal' : (y x : EReal) - f x ≤ (y xStar : EReal) - f xStar := by
        rw [hxStar_f_eq, hfx_eq]
        rw [← EReal.coe_sub, ← EReal.coe_sub]
        exact hpair_ereal
      simpa using hpair_ereal'
    · have hxtop : f x = ⊤ := by
        exact le_antisymm le_top (not_lt.mp (by simpa [mem_effective_domain] using hx))
      simp [hxtop]
  have htop : conjugate_function_strongDual f y < ⊤ := by
    have hfinite_rhs : (y xStar : EReal) - f xStar < ⊤ := by
      rw [hxStar_f_eq]
      simpa [EReal.coe_sub] using EReal.coe_lt_top (y xStar - (f xStar).toReal)
    exact lt_of_le_of_lt hbound hfinite_rhs
  refine ⟨?_, htop⟩
  exact conjugate_function_ne_bot f hf_proper y

/-- Helper for Theorem 5.26 direct proof repair: the real-valued conjugate has derivative given by
the affine-maximizer point. -/
private lemma hasFDerivAt_toRealConjugate_of_affineMinusMaximizer
    (σ : ℝ) (hσ : 0 < σ) (f : E → EReal) (hf_proper : IsProperExtendedRealFunction f)
    (hclosed : LowerSemicontinuous f)
    (hstrong : StrongConvexOn (effective_domain f) σ (fun x ↦ (f x).toReal))
    (y : StrongDual ℝ E) :
    HasFDerivAt
      (fun z : StrongDual ℝ E ↦ (conjugate_function_strongDual f z).toReal)
      (NormedSpace.inclusionInDoubleDual ℝ E
        (affineMinusMaximizer σ hσ f hf_proper hclosed hstrong y))
      y := by
  let T : StrongDual ℝ E → E := affineMinusMaximizer σ hσ f hf_proper hclosed hstrong
  have hT_max :
      ∀ y : StrongDual ℝ E, IsMaxOn (fun z ↦ (y z : EReal) - f z) Set.univ (T y) := by
    intro y'
    simpa [T] using affineMinusMaximizer_isMaxOn σ hσ f hf_proper hclosed hstrong y'
  have hT_sub :
      ∀ y : StrongDual ℝ E, ((y : StrongDual ℝ E) : Module.Dual ℝ E) ∈ ∂ f(T y) := by
    intro y'
    simpa [T] using affineMinusMaximizer_mem_subdifferential σ hσ f hf_proper hclosed hstrong y'
  have hT_lip :
      ∀ y₁ y₂ : StrongDual ℝ E,
        ‖T y₁ - T y₂‖ ≤ (1 / σ) * ‖y₁ - y₂‖ := by
    intro y₁ y₂
    simpa [T] using affineMinusMaximizer_lipschitz σ hσ f hf_proper hclosed hstrong y₁ y₂
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  let L : StrongDual ℝ E →L[ℝ] ℝ := NormedSpace.inclusionInDoubleDual ℝ E (T y)
  have hT_eff :
      ∀ z : StrongDual ℝ E, T z ∈ effective_domain f := by
    intro z
    exact (mem_subdifferential.mp (hT_sub z)).1
  have hconj_eq :
      ∀ z : StrongDual ℝ E,
        conjugate_function_strongDual f z = (z (T z) : EReal) - f (T z) := by
    intro z
    simpa [conjugate_function_strongDual_apply] using
      (conjugate_function_eq_iff_isMaxOn_pairing_sub_function f (T z) z).2 (hT_max z)
  have hconj_coe :
      ∀ z : StrongDual ℝ E,
        conjugate_function_strongDual f z =
          (((conjugate_function_strongDual f z).toReal : ℝ) : EReal) := by
    intro z
    have hfz :
        f (T z) = (((f (T z)).toReal : ℝ) : EReal) :=
      (EReal.coe_toReal (ne_of_lt (mem_effective_domain.mp (hT_eff z)))
        (hf_proper.ne_bot (T z))).symm
    have htop : conjugate_function_strongDual f z ≠ ⊤ := by
      rw [hconj_eq z, hfz, ← EReal.coe_sub]
      exact EReal.coe_ne_top _
    exact (EReal.coe_toReal htop (conjugate_function_ne_bot f hf_proper z)).symm
  have hconj_toReal :
      ∀ z : StrongDual ℝ E,
        (conjugate_function_strongDual f z).toReal = z (T z) - (f (T z)).toReal := by
    intro z
    rw [hconj_eq z]
    simpa using
      (EReal.toReal_sub
        (EReal.coe_ne_top _)
        (EReal.coe_ne_bot _)
        (ne_of_lt (mem_effective_domain.mp (hT_eff z)))
        (hf_proper.ne_bot (T z)))
  have hbig :
      (fun h : StrongDual ℝ E ↦
        (conjugate_function_strongDual f (y + h)).toReal -
          (conjugate_function_strongDual f y).toReal - L h) =O[𝓝 0]
        (fun h : StrongDual ℝ E ↦ ‖h‖ ^ (2 : ℕ)) := by
    refine Asymptotics.IsBigO.of_bound (1 / σ) (Filter.Eventually.of_forall ?_)
    intro h
    have hy_eq :
        conjugate_function_strongDual f y =
          (y (T y) : EReal) - f (T y) := by
      exact hconj_eq y
    have hy_real :
        (conjugate_function_strongDual f y).toReal = y (T y) - (f (T y)).toReal := by
      exact hconj_toReal y
    have hyh_term :
        ((y + h) (T y) : EReal) - f (T y) ≤
          conjugate_function_strongDual f (y + h) := by
      rw [conjugate_function_strongDual_apply, conjugate_function_apply]
      exact le_sSup (Set.mem_range_self (T y))
    have hnonneg :
        0 ≤
          (conjugate_function_strongDual f (y + h)).toReal -
            (conjugate_function_strongDual f y).toReal - L h := by
      have hyh_real :
          (y + h) (T y) - (f (T y)).toReal ≤
            (conjugate_function_strongDual f (y + h)).toReal := by
        have hfy :
            f (T y) = (((f (T y)).toReal : ℝ) : EReal) :=
          (EReal.coe_toReal (ne_of_lt (mem_effective_domain.mp (hT_eff y)))
            (hf_proper.ne_bot (T y))).symm
        have hyh_term' := hyh_term
        rw [hfy, hconj_coe (y + h), ← EReal.coe_sub] at hyh_term'
        exact EReal.coe_le_coe_iff.mp hyh_term'
      have hL_apply : L h = h (T y) := by
        rfl
      have hyh_apply : (y + h) (T y) = y (T y) + h (T y) := by
        simp
      have hyh_real' :
          y (T y) + h (T y) - (f (T y)).toReal ≤
            (conjugate_function_strongDual f (y + h)).toReal := by
        simpa [hyh_apply] using hyh_real
      rw [hy_real, hL_apply]
      linarith
    have hyh_eq :
        conjugate_function_strongDual f (y + h) =
          (((y + h) (T (y + h)) : ℝ) : EReal) - f (T (y + h)) := by
      exact hconj_eq (y + h)
    have hy_term :
        (y (T (y + h)) : EReal) - f (T (y + h)) ≤
          conjugate_function_strongDual f y := by
      rw [conjugate_function_strongDual_apply, conjugate_function_apply]
      exact le_sSup (Set.mem_range_self (T (y + h)))
    have hy_upper :
        (conjugate_function_strongDual f (y + h)).toReal -
            (conjugate_function_strongDual f y).toReal - L h ≤
          h (T (y + h) - T y) := by
      have hyh_real :
          (conjugate_function_strongDual f (y + h)).toReal =
            (y + h) (T (y + h)) - (f (T (y + h))).toReal := by
        exact hconj_toReal (y + h)
      have hy_real' :
          y (T (y + h)) - (f (T (y + h))).toReal ≤
            (conjugate_function_strongDual f y).toReal := by
        have hfyh :
            f (T (y + h)) = (((f (T (y + h))).toReal : ℝ) : EReal) :=
          (EReal.coe_toReal (ne_of_lt (mem_effective_domain.mp (hT_eff (y + h))))
            (hf_proper.ne_bot (T (y + h)))).symm
        have hy_term' := hy_term
        rw [hfyh, hconj_coe y, ← EReal.coe_sub] at hy_term'
        exact EReal.coe_le_coe_iff.mp hy_term'
      have hL_apply : L h = h (T y) := by
        rfl
      have hyh_apply :
          (y + h) (T (y + h)) = y (T (y + h)) + h (T (y + h)) := by
        simp
      have hyh_upper' :
          (conjugate_function_strongDual f (y + h)).toReal ≤
            (conjugate_function_strongDual f y).toReal + h (T (y + h)) := by
        rw [hyh_real, hyh_apply]
        linarith
      have hh_eval :
          h (T (y + h) - T y) = h (T (y + h)) - h (T y) := by
        simp
      rw [hL_apply, hh_eval]
      linarith
    have hquad :
        (conjugate_function_strongDual f (y + h)).toReal -
            (conjugate_function_strongDual f y).toReal - L h ≤
          (1 / σ) * ‖h‖ ^ (2 : ℕ) := by
      have hstep :
          (conjugate_function_strongDual f (y + h)).toReal -
              (conjugate_function_strongDual f y).toReal - L h ≤
            ‖h‖ * ‖T (y + h) - T y‖ := by
        exact le_trans hy_upper <|
          le_trans (le_abs_self _) (h.le_opNorm (T (y + h) - T y))
      have hlip :
          ‖h‖ * ‖T (y + h) - T y‖ ≤
            ‖h‖ * ((1 / σ) * ‖(y + h) - y‖) := by
        exact mul_le_mul_of_nonneg_left (hT_lip (y + h) y) (norm_nonneg h)
      have hnorm :
          ‖h‖ * ((1 / σ) * ‖(y + h) - y‖) = (1 / σ) * ‖h‖ ^ (2 : ℕ) := by
        simp [pow_two, mul_left_comm]
      exact (le_trans hstep hlip).trans_eq hnorm
    have habs :
        ‖(conjugate_function_strongDual f (y + h)).toReal -
            (conjugate_function_strongDual f y).toReal - L h‖ ≤
          (1 / σ) * ‖‖h‖ ^ (2 : ℕ)‖ := by
      have hpow_nonneg : 0 ≤ ‖h‖ ^ (2 : ℕ) := by
        positivity
      have hnorm_eq :
          ‖(conjugate_function_strongDual f (y + h)).toReal -
              (conjugate_function_strongDual f y).toReal - L h‖ =
            (conjugate_function_strongDual f (y + h)).toReal -
              (conjugate_function_strongDual f y).toReal - L h := by
        simpa using (Real.norm_of_nonneg hnonneg)
      rw [hnorm_eq]
      simpa [Real.norm_of_nonneg hpow_nonneg] using hquad
    exact habs
  have hsmallPow :
      (fun h : StrongDual ℝ E ↦ ‖h‖ ^ (2 : ℕ)) =o[𝓝 0] fun h ↦ h := by
    simpa using
      (Asymptotics.isLittleO_norm_pow_id (E' := StrongDual ℝ E) (n := 2) (by norm_num))
  simpa [L] using (hbig.trans_isLittleO hsmallPow)

/-- Theorem 5.26 (2): if `f : E → EReal` is proper, closed, and `σ`-strongly convex, then the
real-valued Fenchel conjugate on `StrongDual ℝ E` is `(1 / σ)`-smooth on `Set.univ`. -/
theorem is_l_smooth_on_toReal_conjugate_function_strongDual_of_proper_closed_strongConvexOn
    (σ : ℝ) (hσ : 0 < σ) (f : E → EReal) (hf_proper : IsProperExtendedRealFunction f)
    (hclosed : LowerSemicontinuous f)
    (hstrong : StrongConvexOn (effective_domain f) σ (fun x ↦ (f x).toReal)) :
    is_l_smooth_on
      (fun y : StrongDual ℝ E ↦ (conjugate_function_strongDual f y).toReal)
      Set.univ
      (Real.toNNReal (1 / σ)) := by
  let T : StrongDual ℝ E → E := affineMinusMaximizer σ hσ f hf_proper hclosed hstrong
  have hT_lip :
      ∀ y₁ y₂ : StrongDual ℝ E,
        ‖T y₁ - T y₂‖ ≤ (1 / σ) * ‖y₁ - y₂‖ := by
    intro y₁ y₂
    simpa [T] using affineMinusMaximizer_lipschitz σ hσ f hf_proper hclosed hstrong y₁ y₂
  rw [is_l_smooth_on_iff]
  refine ⟨?_, ?_⟩
  · intro y _hy
    exact
      (hasFDerivAt_toRealConjugate_of_affineMinusMaximizer
        σ hσ f hf_proper hclosed hstrong y).differentiableAt
  · intro y _hy z _hz
    have hyz :
        fderiv ℝ (fun y : StrongDual ℝ E ↦ (conjugate_function_strongDual f y).toReal) y =
          NormedSpace.inclusionInDoubleDual ℝ E (T y) := by
      simpa [T] using
        (hasFDerivAt_toRealConjugate_of_affineMinusMaximizer
          σ hσ f hf_proper hclosed hstrong y).fderiv
    have hzz :
        fderiv ℝ (fun y : StrongDual ℝ E ↦ (conjugate_function_strongDual f y).toReal) z =
          NormedSpace.inclusionInDoubleDual ℝ E (T z) := by
      simpa [T] using
        (hasFDerivAt_toRealConjugate_of_affineMinusMaximizer
          σ hσ f hf_proper hclosed hstrong z).fderiv
    rw [hyz, hzz]
    calc
      ‖NormedSpace.inclusionInDoubleDual ℝ E (T y) -
          NormedSpace.inclusionInDoubleDual ℝ E (T z)‖
          = ‖NormedSpace.inclusionInDoubleDual ℝ E (T y - T z)‖ := by
              simp
      _ = ‖T y - T z‖ := by
            exact
              (NormedSpace.inclusionInDoubleDualLi (𝕜 := ℝ) (E := E)).norm_map (T y - T z)
      _ ≤ (1 / σ) * ‖y - z‖ := hT_lip y z
      _ = ((Real.toNNReal (1 / σ) : NNReal) : ℝ) * ‖y - z‖ := by
            have hσinv_nonneg : 0 ≤ 1 / σ := by
              positivity
            have hσnn : ((Real.toNNReal (1 / σ) : NNReal) : ℝ) = 1 / σ := by
              simpa using
                congrArg (fun r : NNReal => (r : ℝ)) (Real.toNNReal_of_nonneg hσinv_nonneg)
            rw [hσnn]

end

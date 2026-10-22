/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Order.Filter.Extr
import Mathlib.Topology.Semicontinuity.Basic
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_7
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_4
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_7_1
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_3
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_30
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Definition_5_16

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

-- Semantic recall: this file is `source-facing`. The Chapter 5 owner
-- `is_strongly_convex_function f σ` packages the textbook strong-convexity assumptions, while
-- `IsMinOn` is the canonical minimizer predicate. Theorem 5.25 records the existence, uniqueness,
-- and quadratic-growth consequences of that source-facing owner.

-- Proof sketch: choose `x₀ ∈ effective_domain f` from `hdom`. The Chapter 5 owner hypothesis `hf`
-- exposes the canonical bridge `StrongConvexOn (effective_domain f) σ (fun x ↦ (f x).toReal)`,
-- so uniqueness comes from strict convexity of the real-valued restriction. Existence follows from
-- the coercive quadratic lower bound implied by strong convexity, together with lower
-- semicontinuity and finite-dimensional compactness of a suitable sublevel set.
omit [FiniteDimensional ℝ E] in
/-- Helper for Theorem 5.25: a strongly convex extended-real-valued function is convex in the
Chapter 2 source-facing sense. -/
lemma isConvexFunction_of_isStronglyConvex
    {f : E → EReal} {σ : ℝ} (hf : is_strongly_convex_function f σ) :
    is_convex_function f := by
  -- Transport the Chapter 5 strong-convex owner to convexity of the real-valued restriction.
  refine (is_convex_function_iff_convexOn_toReal (f := f) (fun x _ ↦ hf.ne_bot x)).2 ?_
  have hstrict :
      StrictConvexOn ℝ (effective_domain f) (fun x ↦ (f x).toReal) :=
    (strongConvexOn_toReal_of_is_strongly_convex_function hf).strictConvexOn hf.sigma_pos
  -- Strict convexity is stronger than the convexity bridge required by Chapter 2.
  exact hstrict.convexOn

omit [FiniteDimensional ℝ E] in
/-- Helper for Theorem 5.25: one subgradient witness for a strongly convex function bounds every
real sublevel set, which is the coercivity input needed for the global-minimizer theorem. -/
lemma strongConvexSubgradientLowerBound
    {f : E → EReal} {σ : ℝ} (hσ : 0 < σ) (h_ne_bot : ∀ z, f z ≠ ⊥)
    (hstrong : StrongConvexOn (effective_domain f) σ (fun z ↦ (f z).toReal)) :
    ∀ x : E, ∀ g ∈ ∂ f(x), ∀ y ∈ effective_domain f,
      f y ≥ f x + ((g (y - x) + (σ / 2) * ‖y - x‖ ^ (2 : ℕ) : ℝ) : EReal) := by
  intro x g hg y hy
  have hx : x ∈ effective_domain f := (mem_subdifferential.mp hg).1
  by_cases hxy : x = y
  · -- On the diagonal the quadratic term vanishes, so the support bound is immediate.
    subst y
    rw [ge_iff_le]
    have hfx :
        f x = (((f x).toReal : ℝ) : EReal) := by
      exact (EReal.coe_toReal (ne_of_lt hx) (h_ne_bot x)).symm
    rw [hfx]
    simp
  · -- Route correction: derive the quadratic support bound directly from the strong-convex owner
    -- by combining the subgradient slope estimate with the segment inequality on short segments.
    let fx : ℝ := (f x).toReal
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
        linarith
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
    -- Convert the real inequality back to the original `EReal` support estimate.
    rw [ge_iff_le, hfx, hfy]
    have hsum_real : fx + (g (y - x) + q) ≤ fy := by
      linarith
    have hsum_ereal :
        (((fx + (g (y - x) + q) : ℝ) : EReal)) ≤ ((fy : ℝ) : EReal) :=
      EReal.coe_le_coe hsum_real
    simpa [fx, fy, q, norm_sub_rev, EReal.coe_add, add_assoc] using hsum_ereal

/-- Helper for Theorem 5.25: one subgradient witness for a strongly convex function bounds every
real sublevel set, which is the coercivity input needed for the global-minimizer theorem. -/
lemma boundedRealSublevelSets_of_stronglyConvexSubgradient
    {f : E → EReal} {σ : ℝ} (hf : is_strongly_convex_function f σ)
    (x0 : E) (hx0 : x0 ∈ effective_domain f) {g : Module.Dual ℝ E} (hg : g ∈ ∂f(x0)) :
    ∀ a : ℝ, Bornology.IsBounded {x | f x ≤ (a : EReal)} := by
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
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv
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
    -- Convert the norm estimate into the metric closed-ball bound.
    simpa [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev, R] using hnorm
  -- Once the whole sublevel set sits in one closed ball, boundedness is immediate.
  exact Metric.isBounded_closedBall.subset hsubset

/-- Theorem 5.25 (1): a closed `σ`-strongly convex extended-real-valued function with nonempty
effective domain has a unique global minimizer. The no-`-∞` and positivity clauses are carried by
the source-facing owner `is_strongly_convex_function f σ`, while domain nonemptiness remains an
explicit hypothesis because it is not part of that owner. -/
theorem existsUnique_isMinOn_univ_of_closed_strongly_convex
    {f : E → EReal} {σ : ℝ} (hf : is_strongly_convex_function f σ)
    (hdom : (effective_domain f).Nonempty) (hclosed : LowerSemicontinuous f) :
    ∃! xStar : E, IsMinOn f Set.univ xStar := by
  have hproper : IsProperExtendedRealFunction f := ⟨hf.ne_bot, hdom⟩
  have hconv : is_convex_function f := isConvexFunction_of_isStronglyConvex hf
  -- First choose one effective-domain point with a subgradient.
  obtain ⟨x0, hx0, hg_nonempty⟩ :=
    exists_subdifferentiable_point_in_effective_domain_of_convex_of_effective_domain_nonempty
      f hconv hdom
  obtain ⟨g, hg⟩ := hg_nonempty
  have hlevel :
      ∀ a : ℝ, Bornology.IsBounded {x | f x ≤ (a : EReal)} :=
    boundedRealSublevelSets_of_stronglyConvexSubgradient hf x0 hx0 hg
  -- The bounded real sublevel sets and lower semicontinuity give one global minimizer.
  obtain ⟨xStar, hxStar, hxStarMin⟩ :=
    exists_isMinOn_univ_of_bounded_real_sublevelSets f hproper hclosed hlevel
  refine ⟨xStar, hxStarMin, ?_⟩
  intro y hy
  have hstrict :
      StrictConvexOn ℝ (effective_domain f) (fun z ↦ (f z).toReal) :=
    (strongConvexOn_toReal_of_is_strongly_convex_function hf).strictConvexOn hf.sigma_pos
  have hy_zero : (0 : Module.Dual ℝ E) ∈ ∂ f(y) :=
    (isMinOn_univ_iff_zero_mem_subdifferential (f := f) hdom).mp hy
  have hy_dom : y ∈ effective_domain f := (mem_subdifferential.mp hy_zero).1
  have hxStarMinReal :
      IsMinOn (fun z ↦ (f z).toReal) (effective_domain f) xStar := by
    rw [isMinOn_iff]
    intro z hz
    have hxStar_coe : (((f xStar).toReal : ℝ) : EReal) = f xStar := by
      exact EReal.coe_toReal (ne_of_lt (mem_effective_domain.mp hxStar)) (hf.ne_bot xStar)
    have hz_coe : (((f z).toReal : ℝ) : EReal) = f z := by
      exact EReal.coe_toReal (ne_of_lt (mem_effective_domain.mp hz)) (hf.ne_bot z)
    have hmin : f xStar ≤ f z := (isMinOn_iff.mp hxStarMin) z (by simp)
    rw [← hxStar_coe, ← hz_coe] at hmin
    exact_mod_cast hmin
  have hyMinReal :
      IsMinOn (fun z ↦ (f z).toReal) (effective_domain f) y := by
    rw [isMinOn_iff]
    intro z hz
    have hy_coe : (((f y).toReal : ℝ) : EReal) = f y := by
      exact EReal.coe_toReal (ne_of_lt (mem_effective_domain.mp hy_dom)) (hf.ne_bot y)
    have hz_coe : (((f z).toReal : ℝ) : EReal) = f z := by
      exact EReal.coe_toReal (ne_of_lt (mem_effective_domain.mp hz)) (hf.ne_bot z)
    have hmin : f y ≤ f z := (isMinOn_iff.mp hy) z (by simp)
    rw [← hy_coe, ← hz_coe] at hmin
    exact_mod_cast hmin
  -- Strict convexity identifies any two global minimizers once both lie in the effective domain.
  exact (StrictConvexOn.eq_of_isMinOn (x := xStar) (y := y) hstrict
    hxStarMinReal hyMinReal hxStar hy_dom).symm

-- Proof sketch: unfold the segment inequality from `hf` at `xStar` and `x`, then use the global
-- minimizing property of `xStar` on `Set.univ` to bound the intermediate point values from below by
-- `f xStar`. Rearranging the resulting Jensen estimate yields the quadratic growth inequality.
omit [FiniteDimensional ℝ E] in
/-- Theorem 5.25 (2): if `xStar` is a global minimizer of a `σ`-strongly convex extended-real-
valued function, then every `x ∈ effective_domain f` satisfies the quadratic growth bound above
the minimum. This is the extended-real rendering of the textbook estimate
`f(x) - f(x^*) ≥ (σ / 2) ‖x - x^*‖²`. -/
theorem lower_quadratic_bound_of_isMinOn_of_strongly_convex
    {f : E → EReal} {σ : ℝ} (hf : is_strongly_convex_function f σ)
    (xStar : E) (hxStar : IsMinOn f Set.univ xStar) (x : E) (hx : x ∈ effective_domain f) :
    f x ≥ f xStar + ((((σ / 2) * ‖x - xStar‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
  have hzero : (0 : Module.Dual ℝ E) ∈ ∂ f(xStar) :=
    (isMinOn_univ_iff_zero_mem_subdifferential (f := f) ⟨x, hx⟩).mp hxStar
  have hquad :=
    strongConvexSubgradientLowerBound hf.sigma_pos hf.ne_bot
      (strongConvexOn_toReal_of_is_strongly_convex_function hf)
  -- Specialize the quadratic support inequality at the minimizer, where the subgradient is zero.
  simpa using hquad xStar (0 : Module.Dual ℝ E) hzero x hx

end

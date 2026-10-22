/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_4
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_7_1
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_18
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_3
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_30
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Definition_5_16
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Lemma_5_20
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Definition_9_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped Pointwise

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {ψ ω : E → EReal} {σ : ℝ}

/- Lemma 9.7 is `source-facing` in the Chapter 9 mirror-descent setup. The owner abstraction for
the mirror-map assumptions is already the project class `IsBregmanPotentialOn`, instantiated on the
constraint set `dom(ψ) = effective_domain ψ`; the conclusion itself is the textbook minimizer
statement, expressed directly through mathlib's `IsMinOn` and the Chapter 3 owner
`subdifferential_domain`. -/

/-- Helper for Lemma 9.7: the constrained-potential spelling
`x ↦ (ω + δ_(effective_domain ψ))(x) + ψ(x)` agrees pointwise with the raw composite objective
`x ↦ ψ(x) + ω(x)`. -/
private theorem constrainedPotentialAdd_psi_eq_compositeObjective
    (hω : IsBregmanPotentialOn ω (effective_domain ψ) σ) :
    (fun x ↦ ω x + (δ_ (effective_domain ψ)) x + ψ x) = (fun x ↦ ψ x + ω x) := by
  funext x
  by_cases hx : x ∈ effective_domain ψ
  · -- On feasible points the indicator vanishes, so only commutativity of addition remains.
    simp [extendedIndicator_of_mem hx, add_comm]
  · have hψ_top : ψ x = ⊤ := le_antisymm le_top (not_lt.mp hx)
    have hinner_top : (ω + δ_ (effective_domain ψ)) x = ⊤ := by
      simpa [Pi.add_apply, extendedIndicator_of_not_mem hx] using
        EReal.add_top_of_ne_bot (hω.ne_bot x)
    have hright_top : ψ x + ω x = ⊤ := by
      rw [hψ_top]
      simpa using EReal.top_add_of_ne_bot (hω.ne_bot x)
    calc
      ω x + (δ_ (effective_domain ψ)) x + ψ x = ⊤ := by
        simpa [Pi.add_apply, extendedIndicator_of_not_mem hx, hψ_top, add_assoc] using
          EReal.add_top_of_ne_bot (hω.ne_bot x)
      _ = ψ x + ω x := hright_top.symm

/-- Helper for Lemma 9.7: the raw composite objective inherits `σ`-strong convexity from the
constrained potential `ω + δ_(effective_domain ψ)` and the convex perturbation `ψ`. -/
private theorem compositeObjectiveStronglyConvex
    (hω : IsBregmanPotentialOn ω (effective_domain ψ) σ)
    (hψ_proper : IsProperExtendedRealFunction ψ) (hψ_convex : is_convex_function ψ) :
    is_strongly_convex_function (fun x ↦ ψ x + ω x) σ := by
  have hindicator_ne_bot : ∀ x, (δ_ (effective_domain ψ)) x ≠ ⊥ := by
    intro x
    by_cases hx : x ∈ effective_domain ψ
    · simp [extendedIndicator_of_mem hx]
    · simp [extendedIndicator_of_not_mem hx]
  have hconstrained :
      is_strongly_convex_function (fun x ↦ (ω + δ_ (effective_domain ψ)) x) σ := by
    -- Package the stored `StrongConvexOn` owner for `ω + δ_(effective_domain ψ)` back into the
    -- Chapter 5 strong-convexity predicate.
    refine (is_strongly_convex_function_iff_strongConvexOn_toReal).mpr ?_
    refine ⟨hω.sigma_pos, ?_, hω.strongConvexOn_add_indicator⟩
    intro x
    rw [Pi.add_apply, EReal.add_ne_bot_iff]
    exact ⟨hω.ne_bot x, hindicator_ne_bot x⟩
  have hsum :
      is_strongly_convex_function
        (fun x ↦ (ω + δ_ (effective_domain ψ)) x + ψ x) σ :=
    is_strongly_convex_function_add_of_is_convex_function
      hconstrained hψ_convex hψ_proper.ne_bot
  -- Rewrite the constrained-potential spelling back to the composite objective used in Lemma 9.7.
  simpa [Pi.add_apply, constrainedPotentialAdd_psi_eq_compositeObjective hω] using hsum

/-- Helper for Lemma 9.7: the composite objective is proper because `ψ` supplies one feasible
point and `ω` is finite on `effective_domain ψ`. -/
private theorem compositeObjectiveProper
    (hω : IsBregmanPotentialOn ω (effective_domain ψ) σ)
    (hψ_proper : IsProperExtendedRealFunction ψ) :
    IsProperExtendedRealFunction (fun x ↦ ψ x + ω x) := by
  refine ⟨?_, ?_⟩
  · intro x
    rw [EReal.add_ne_bot_iff]
    exact ⟨hψ_proper.ne_bot x, hω.ne_bot x⟩
  · rcases hψ_proper.effective_domain_nonempty with ⟨x, hxψ⟩
    have hxω : x ∈ effective_domain ω := hω.subset_effective_domain hxψ
    refine ⟨x, ?_⟩
    exact mem_effective_domain.mpr <|
      EReal.add_lt_top (ne_of_lt (mem_effective_domain.mp hxψ))
        (ne_of_lt (mem_effective_domain.mp hxω))

/-- Helper for Lemma 9.7: lower semicontinuity of `ψ + ω` comes from lower semicontinuity of the
summands and the fact that neither summand ever takes the value `-∞`. -/
private theorem compositeObjectiveClosed
    (hω : IsBregmanPotentialOn ω (effective_domain ψ) σ)
    (hψ_proper : IsProperExtendedRealFunction ψ) (hψ_closed : LowerSemicontinuous ψ) :
    LowerSemicontinuous (fun x ↦ ψ x + ω x) := by
  -- Addition is continuous at every point once the `-∞` branch is ruled out for both summands.
  refine hψ_closed.add' hω.closed ?_
  intro x
  exact EReal.continuousAt_add (.inr (hω.ne_bot x)) (.inl (hψ_proper.ne_bot x))

/-- Helper for Lemma 9.7: a strong-convexity subgradient inequality in the normed-space setting. -/
private theorem strongConvexSubgradientLowerBoundNormed
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
    have hfx : f x = (((f x).toReal : ℝ) : EReal) := by
      exact (EReal.coe_toReal (ne_of_lt hx) (h_ne_bot x)).symm
    rw [hfx]
    simp
  · -- Route correction: derive the quadratic lower bound from the strong-convex owner directly,
    -- instead of trying to recover it through an unavailable inner-product-space wrapper.
    let fx : ℝ := (f x).toReal
    let fy : ℝ := (f y).toReal
    let q : ℝ := (σ / 2) * ‖x - y‖ ^ (2 : ℕ)
    have hq_pos : 0 < q := by
      dsimp [q]
      have hnorm_pos : 0 < ‖x - y‖ := by
        refine norm_pos_iff.mpr ?_
        exact sub_ne_zero.mpr hxy
      positivity
    have hfx : f x = ((fx : ℝ) : EReal) := by
      exact (EReal.coe_toReal (ne_of_lt hx) (h_ne_bot x)).symm
    have hfy : f y = ((fy : ℝ) : EReal) := by
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
    -- Convert the real inequality back to the original extended-real support estimate.
    rw [ge_iff_le, hfx, hfy]
    have hsum_real : fx + (g (y - x) + q) ≤ fy := by
      linarith
    have hsum_ereal :
        (((fx + (g (y - x) + q) : ℝ) : EReal)) ≤ ((fy : ℝ) : EReal) :=
      EReal.coe_le_coe hsum_real
    simpa [fx, fy, q, norm_sub_rev, EReal.coe_add, add_assoc] using hsum_ereal

/-- Helper for Lemma 9.7: one subgradient witness bounds every real sublevel set of a strongly
convex extended-real-valued function. -/
private theorem boundedRealSublevelSets_ofStronglyConvexSubgradientNormed
    {f : E → EReal} {σ : ℝ} (hf : is_strongly_convex_function f σ)
    (x0 : E) (hx0 : x0 ∈ effective_domain f) {g : Module.Dual ℝ E} (hg : g ∈ ∂ f(x0)) :
    ∀ a : ℝ, Bornology.IsBounded {x | f x ≤ (a : EReal)} := by
  intro a
  let gCLM : E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap g
  let c : ℝ := a - (f x0).toReal + ‖gCLM‖ ^ (2 : ℕ) / σ
  let R : ℝ := Real.sqrt (4 * max c 0 / σ)
  have hσ : 0 < σ := hf.sigma_pos
  have hx0_coe : (((f x0).toReal : ℝ) : EReal) = f x0 := by
    exact EReal.coe_toReal (ne_of_lt (mem_effective_domain.mp hx0)) (hf.ne_bot x0)
  have hquad :=
    strongConvexSubgradientLowerBoundNormed hσ hf.ne_bot
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

/-- Helper for Lemma 9.7: in finite-dimensional normed spaces, closed strongly convex extended-
real-valued functions with nonempty effective domain have unique global minimizers. -/
private theorem existsUnique_isMinOn_univ_of_closed_strongly_convex_normed
    {f : E → EReal} {σ : ℝ} (hf : is_strongly_convex_function f σ)
    (hdom : (effective_domain f).Nonempty) (hclosed : LowerSemicontinuous f) :
    ∃! xStar : E, IsMinOn f Set.univ xStar := by
  have hproper : IsProperExtendedRealFunction f := ⟨hf.ne_bot, hdom⟩
  have hconv : is_convex_function f := by
    refine (is_convex_function_iff_convexOn_toReal (f := f) (fun x _ ↦ hf.ne_bot x)).2 ?_
    exact
      ((strongConvexOn_toReal_of_is_strongly_convex_function hf).strictConvexOn hf.sigma_pos).convexOn
  -- First choose one effective-domain point with a subgradient to control the sublevel geometry.
  obtain ⟨x0, hx0, hg_nonempty⟩ :=
    exists_subdifferentiable_point_in_effective_domain_of_convex_of_effective_domain_nonempty
      f hconv hdom
  obtain ⟨g, hg⟩ := hg_nonempty
  have hlevel :
      ∀ a : ℝ, Bornology.IsBounded {x | f x ≤ (a : EReal)} :=
    boundedRealSublevelSets_ofStronglyConvexSubgradientNormed hf x0 hx0 hg
  -- Bounded real sublevel sets plus lower semicontinuity yield one global minimizer.
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

/-- Helper for Lemma 9.7: every global minimizer of `x ↦ ψ x + ω x` belongs to `dom(ψ)`. -/
private theorem compositeMinimizer_mem_effectiveDomain
    (hω : IsBregmanPotentialOn ω (effective_domain ψ) σ)
    (hψ_proper : IsProperExtendedRealFunction ψ)
    {xStar : E} (hxStar : IsMinOn (fun x ↦ ψ x + ω x) Set.univ xStar) :
    xStar ∈ effective_domain ψ := by
  -- Compare the minimizer with one known feasible point coming from properness of `ψ`.
  rcases hψ_proper.effective_domain_nonempty with ⟨x0, hx0ψ⟩
  have hx0ω : x0 ∈ effective_domain ω := hω.subset_effective_domain hx0ψ
  have hmin : ψ xStar + ω xStar ≤ ψ x0 + ω x0 := by
    simpa using (isMinOn_iff.mp hxStar) x0 (by simp)
  have hsum_finite_rhs : ψ x0 + ω x0 < ⊤ := by
    exact EReal.add_lt_top (ne_of_lt (mem_effective_domain.mp hx0ψ))
      (ne_of_lt (mem_effective_domain.mp hx0ω))
  have hsum_finite : ψ xStar + ω xStar < ⊤ := lt_of_le_of_lt hmin hsum_finite_rhs
  by_contra hxStar_dom
  have hψ_top : ψ xStar = ⊤ := le_antisymm le_top (not_lt.mp hxStar_dom)
  have hsum_top : ψ xStar + ω xStar = ⊤ := by
    rw [hψ_top]
    simpa using EReal.top_add_of_ne_bot (hω.ne_bot xStar)
  exact (ne_of_lt hsum_finite) hsum_top

/-- Helper for Lemma 9.7: any explicit splitting of the zero subgradient of `ψ + ω` at `xStar`
into a `ψ`-subgradient and an `ω`-subgradient already certifies `xStar ∈ dom(∂ω)`. -/
private theorem mem_subdifferentialDomain_of_zeroSubgradientSplit
    {xStar : E}
    (hsplit :
      ∃ gψ gω : Module.Dual ℝ E,
        gψ ∈ ∂ψ(xStar) ∧
        gω ∈ ∂ω(xStar) ∧
        gψ + gω = (0 : Module.Dual ℝ E)) :
    xStar ∈ subdifferential_domain ω := by
  rcases hsplit with ⟨_, gω, _, hgω, _⟩
  -- The `ω`-component of the split zero subgradient is already the required witness.
  exact mem_subdifferential_domain.mpr ⟨gω, hgω⟩

/-- Helper for Lemma 9.7: under the intrinsic-interior qualification, the subdifferential of the
binary composite objective `x ↦ ψ x + ω x` splits exactly as `∂ψ(xStar) + ∂ω(xStar)`. -/
private theorem subdifferentialCompositeObjective_eq_sumSubdifferential
    (hω : IsBregmanPotentialOn ω (effective_domain ψ) σ)
    (hψ_proper : IsProperExtendedRealFunction ψ) (hψ_convex : is_convex_function ψ)
    (hqual :
      (intrinsicInterior ℝ (effective_domain ψ) ∩
        intrinsicInterior ℝ (effective_domain ω)).Nonempty)
    (xStar : E) :
    subdifferential (fun x ↦ ψ x + ω x) xStar =
      ∂ψ(xStar) + ∂ω(xStar) := by
  let F : Fin 2 → E → EReal := fun i =>
    match i with
    | 0 => ψ
    | 1 => ω
  have hneBot : ∀ i : Fin 2, ∀ y : E, F i y ≠ ⊥ := by
    intro i y
    fin_cases i
    · simpa [F] using hψ_proper.ne_bot y
    · simpa [F] using hω.ne_bot y
  have hconvF : ∀ i : Fin 2, is_convex_function (F i) := by
    intro i
    fin_cases i
    · simpa [F] using hψ_convex
    · simpa [F] using hω.convex
  have hqualF : (⋂ i : Fin 2, intrinsicInterior ℝ (effective_domain (F i))).Nonempty := by
    rcases hqual with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    -- Repackage the binary intrinsic-interior hypothesis in the finite-family shape used by
    -- the Chapter 3 exact sum rule.
    simp only [Set.mem_iInter]
    intro i
    fin_cases i
    · simpa [F] using hx.1
    · simpa [F] using hx.2
  have hsumBase :
      subdifferential (fun y ↦ ∑ i : Fin 2, F i y) xStar =
        ∑ i : Fin 2, ∂(F i)(xStar) :=
    subdifferential_finset_sum_eq_sum_subdifferential_of_nonempty_iInter_relativeInterior
      (E := E) (ι := Fin 2) (f := F) (x := xStar) hneBot hconvF hqualF
  have hsumLeft : (fun y ↦ ∑ i : Fin 2, F i y) = (fun y ↦ ψ y + ω y) := by
    funext y
    simp [F, Fin.sum_univ_two]
  have hsumRight : (∑ i : Fin 2, ∂(F i)(xStar)) = ∂ψ(xStar) + ∂ω(xStar) := by
    simp [F, Fin.sum_univ_two]
  -- Route correction: rewrite the lifted two-point family back to the textbook binary objective
  -- on both the primal sum and the summed subdifferential.
  calc
    subdifferential (fun x ↦ ψ x + ω x) xStar =
        subdifferential (fun y ↦ ∑ i : Fin 2, F i y) xStar := by
          rw [hsumLeft]
    _ = ∑ i : Fin 2, ∂(F i)(xStar) := hsumBase
    _ = ∂ψ(xStar) + ∂ω(xStar) := hsumRight

/-- Helper for Lemma 9.7: a global minimizer of `x ↦ ψ x + ω x` yields explicit subgradients
`gψ ∈ ∂ψ(xStar)` and `gω ∈ ∂ω(xStar)` satisfying `gψ + gω = 0`. -/
private theorem existsZeroSplitSubgradientOfCompositeMinimizer
    (hω : IsBregmanPotentialOn ω (effective_domain ψ) σ)
    (hψ_proper : IsProperExtendedRealFunction ψ) (hψ_convex : is_convex_function ψ)
    (hqual :
      (intrinsicInterior ℝ (effective_domain ψ) ∩
        intrinsicInterior ℝ (effective_domain ω)).Nonempty)
    {xStar : E} (hxStar : IsMinOn (fun x ↦ ψ x + ω x) Set.univ xStar) :
    ∃ gψ gω : Module.Dual ℝ E,
      gψ ∈ ∂ ψ(xStar) ∧
      gω ∈ ∂ ω(xStar) ∧
      gψ + gω = (0 : Module.Dual ℝ E) := by
  let hproper := compositeObjectiveProper hω hψ_proper
  have hzero :
      (0 : Module.Dual ℝ E) ∈ subdifferential (fun x ↦ ψ x + ω x) xStar := by
    -- Fermat gives stationarity for the unconstrained composite objective once properness
    -- supplies a nonempty effective domain.
    exact
      (isMinOn_univ_iff_zero_mem_subdifferential
        (f := fun x ↦ ψ x + ω x) hproper.effective_domain_nonempty).mp hxStar
  rw [subdifferentialCompositeObjective_eq_sumSubdifferential
    hω hψ_proper hψ_convex hqual] at hzero
  rw [Set.mem_add] at hzero
  rcases hzero with ⟨gψ, hgψ, gω, hgω, hsum⟩
  -- Unpack the pointwise set-sum witness into the explicit split used downstream.
  exact ⟨gψ, gω, hgψ, hgω, hsum⟩

/-- Companion to Lemma 9.7: any global minimizer of the composite objective `x ↦ ψ x + ω x`
lies in `dom(ψ) ∩ dom(∂ ω)` under the intrinsic-interior qualification needed for the Chapter 3
exact sum rule. This exposes the domain-membership consequence separately from the
existence/uniqueness statement, so downstream files can reuse it directly from an `IsMinOn`
hypothesis. -/
theorem composite_minimizer_mem_domains
    (hω : IsBregmanPotentialOn ω (effective_domain ψ) σ)
    (hψ_proper : IsProperExtendedRealFunction ψ) (hψ_convex : is_convex_function ψ)
    (hqual :
      (intrinsicInterior ℝ (effective_domain ψ) ∩
        intrinsicInterior ℝ (effective_domain ω)).Nonempty)
    {xStar : E} (hxStar : IsMinOn (fun x ↦ ψ x + ω x) Set.univ xStar) :
    xStar ∈ effective_domain ψ ∩ subdifferential_domain ω := by
  refine ⟨?_, ?_⟩
  · -- The minimizer is feasible because the composite objective is finite at every minimizer.
    exact compositeMinimizer_mem_effectiveDomain hω hψ_proper hxStar
  · -- Fermat plus the exact sum rule provides an `ω`-subgradient witness at the minimizer.
    exact mem_subdifferentialDomain_of_zeroSubgradientSplit <|
      existsZeroSplitSubgradientOfCompositeMinimizer hω hψ_proper hψ_convex hqual hxStar

/-- Helper for Lemma 9.7: the composite problem has a unique global minimizer, and that minimizer
lies in `dom(ψ)`. -/
private theorem existsUnique_composite_minimizer_mem_effectiveDomain
    (hω : IsBregmanPotentialOn ω (effective_domain ψ) σ)
    (hψ_proper : IsProperExtendedRealFunction ψ) (hψ_closed : LowerSemicontinuous ψ)
    (hψ_convex : is_convex_function ψ) :
    ∃! xStar : E,
      IsMinOn (fun x ↦ ψ x + ω x) Set.univ xStar ∧ xStar ∈ effective_domain ψ := by
  let hstrong :=
    compositeObjectiveStronglyConvex hω hψ_proper hψ_convex
  let hproper :=
    compositeObjectiveProper hω hψ_proper
  let hclosed :=
    compositeObjectiveClosed hω hψ_proper hψ_closed
  rcases existsUnique_isMinOn_univ_of_closed_strongly_convex_normed
      hstrong hproper.effective_domain_nonempty hclosed with
    ⟨xStar, hxStar, huniq⟩
  refine ⟨xStar, ?_, ?_⟩
  · -- Pair the unique minimizer with the already-verified `dom(ψ)` membership.
    exact ⟨hxStar, compositeMinimizer_mem_effectiveDomain hω hψ_proper hxStar⟩
  · intro y hy
    exact huniq y hy.1

-- Proof sketch: use `hω.strongConvexOn_add_indicator` to view `x ↦ ψ x + ω x` as a proper closed
-- `σ`-strongly convex extended-real-valued function on `effective_domain ψ`, then apply the
-- normed-space strong-convex minimizer theorem proved above to obtain a unique global minimizer.
-- The companion theorem `composite_minimizer_mem_domains` supplies the domain-membership
-- conclusion for that minimizer.
/-- Lemma 9.7: if `ω` is a Bregman potential on `dom(ψ)` and `ψ` is proper, closed, and convex,
and the intrinsic interiors of `dom(ψ)` and `dom(ω)` intersect, then the composite problem
`min_x {ψ(x) + ω(x)}` has a unique minimizer, and that minimizer lies in
`dom(ψ) ∩ dom(∂ ω)`. -/
theorem existsUnique_composite_minimizer_mem_domains
    (hω : IsBregmanPotentialOn ω (effective_domain ψ) σ)
    (hψ_proper : IsProperExtendedRealFunction ψ) (hψ_closed : LowerSemicontinuous ψ)
    (hψ_convex : is_convex_function ψ)
    (hqual :
      (intrinsicInterior ℝ (effective_domain ψ) ∩
        intrinsicInterior ℝ (effective_domain ω)).Nonempty) :
    ∃! xStar : E,
      IsMinOn (fun x ↦ ψ x + ω x) Set.univ xStar ∧
        xStar ∈ effective_domain ψ ∩ subdifferential_domain ω := by
  rcases existsUnique_composite_minimizer_mem_effectiveDomain hω hψ_proper hψ_closed hψ_convex with
    ⟨xStar, hxStar, huniq⟩
  refine ⟨xStar, ?_, ?_⟩
  · -- Reuse the previously constructed unique minimizer and upgrade its domain certificate from
    -- `dom(ψ)` to `dom(ψ) ∩ dom(∂ω)` via the companion theorem above.
    refine ⟨hxStar.1, ?_⟩
    exact composite_minimizer_mem_domains hω hψ_proper hψ_convex hqual hxStar.1
  · intro y hy
    -- Uniqueness still depends only on the global minimizer component; the extra
    -- `subdifferential_domain` witness is proof-irrelevant for identifying the optimizer.
    exact huniq y ⟨hy.1, hy.2.1⟩

end

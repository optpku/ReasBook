/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_7
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_8
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_10
import Mathlib.Analysis.Convex.Deriv

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Filter
open scoped Topology

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Lemma 3.2 is a `source-facing` consequence in the chapter directional-derivative API. The owner
objects are the Chapter 3 directional-derivative declarations
`has_directional_derivative_at`/`directional_derivative` together with the Chapter 2 owners
`effective_domain`, `finite_domain`, and `is_convex_function`. Unlike Theorem 3.11, this lemma
does not assume an inner-product or finite-dimensional structure, so its main statement should
remain a direct affine lower bound rather than being collapsed into a subdifferential-max formula.
The reusable owner-side qualification in Chapter 3 is `x ∈ interior (finite_domain f)`; the
textbook `h_ne_bot` plus `x ∈ interior (effective_domain f)` formulation is kept below as a thin
source-facing bridge. -/
-- Semantic recall check: mathlib has related one-variable convex derivative lemmas such as
-- `bddBelow_slope_lt_of_mem_interior`, but this item is a project-specific extended-real
-- directional-derivative statement, so the chapter API remains the correct owner surface here.
recall effective_domain
recall finite_domain
recall is_convex_function
recall directional_derivative

-- Proof sketch: for `y ∈ effective_domain f`, restrict `f` to the segment from `x` to `y`.
-- Convexity gives
-- `(f (x + t • (y - x)) - f x) / t ≤ f y - f x` for every `t ∈ (0, 1)`. Since `x` is an interior
-- point of `finite_domain f`, the right-hand limit of these
-- difference quotients is the directional derivative at `x` along `y - x`, and passing to the
-- limit yields the claimed affine lower bound.
/-- Helper for Lemma 3.2: if a convex extended-real-valued function is finite at one interior
point of its finite domain, then it never takes the value `⊥`. -/
lemma valueNeBotOfMemInteriorFiniteDomain
    (f : E → EReal) (x : E) (hconvex : is_convex_function f)
    (hx : x ∈ interior (finite_domain f)) :
    ∀ y : E, f y ≠ ⊥ := by
  intro y
  have hxfd : x ∈ finite_domain f := interior_subset hx
  by_contra hy_bot
  by_cases hxy : y = x
  · exact hxfd.2 (hxy ▸ hy_bot)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hx)
  let t : ℝ := min 1 (ε / (‖y - x‖ + 1))
  have ht_pos : 0 < t := by
    -- Choose a short step so the translated point stays inside the interior ball around `x`.
    dsimp [t]
    refine lt_min zero_lt_one ?_
    positivity
  have ht_nonneg : 0 ≤ t := ht_pos.le
  have hnorm_lt : ‖(-t) • (y - x)‖ < ε := by
    have hle : t ≤ ε / (‖y - x‖ + 1) := by
      dsimp [t]
      exact min_le_right _ _
    have hden : 0 < ‖y - x‖ + 1 := by positivity
    have hscaled : t * (‖y - x‖ + 1) ≤ ε := by
      have hmul := mul_le_mul_of_nonneg_right hle hden.le
      calc
        t * (‖y - x‖ + 1) ≤ (ε / (‖y - x‖ + 1)) * (‖y - x‖ + 1) := hmul
        _ = ε := by field_simp [hden.ne']
    have hlt_aux : t * ‖y - x‖ < t * (‖y - x‖ + 1) := by
      nlinarith [ht_pos]
    have htv : t * ‖y - x‖ < ε := lt_of_lt_of_le hlt_aux hscaled
    simpa [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht_nonneg] using htv
  let z : E := x + (-t) • (y - x)
  have hz_mem : z ∈ finite_domain f := by
    have hz_ball : z ∈ Metric.ball x ε := by
      -- The translated point is chosen inside the interior ball around `x`.
      simpa [z, Metric.mem_ball, dist_eq_norm, add_sub_cancel_left] using hnorm_lt
    exact interior_subset (hball hz_ball)
  let θ : ℝ := t / (1 + t)
  have hθ : θ ∈ Set.Ioo (0 : ℝ) 1 := by
    -- The convex-combination weight belongs to `(0, 1)`.
    dsimp [θ]
    constructor
    · positivity
    · have ht1 : 0 < 1 + t := by positivity
      have htt : t < 1 + t := by linarith
      exact (div_lt_one ht1).2 htt
  have hz_epi : f z ≤ ((f z).toReal : EReal) := by
    exact EReal.le_coe_toReal (ne_of_lt (mem_effective_domain.mp hz_mem.1))
  have hx_combo : x = θ • y + (1 - θ) • z := by
    -- Rewrite `x` as a strict convex combination of `y` and the nearby finite point `z`.
    have hx_combo' :
        x = (t / (1 + t)) • y + (1 - t / (1 + t)) • (x + (-t) • (y - x)) := by
      have ht1 : (1 + t) ≠ 0 := by positivity
      rw [Convex.combo_eq_smul_sub_add (by ring : t / (1 + t) + (1 - t / (1 + t)) = 1)]
      have hθ' : 1 - t / (1 + t) = 1 / (1 + t) := by
        field_simp [ht1]
        ring
      rw [hθ']
      have hz_sub : (x + (-t) • (y - x)) - y = (1 + t) • (x - y) := by
        calc
          (x + (-t) • (y - x)) - y = x + t • x - (y + t • y) := by
            simp [sub_eq_add_neg]
            abel
          _ = (1 + t) • (x - y) := by
            rw [smul_sub, add_smul, add_smul]
            simp [sub_eq_add_neg, add_comm, add_assoc]
      rw [hz_sub, smul_smul]
      field_simp [ht1]
      simp
    simpa [θ, z] using hx_combo'
  have hepigraph :
      Convex ℝ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)} :=
    (is_convex_function_iff_convex_real_epigraph f).mp hconvex
  have hbelow (R : ℝ) : f x ≤ (R : EReal) := by
    -- Push an arbitrary real height down from `y = ⊥` to `x` through the epigraph convexity.
    let ry : ℝ := (R - (1 - θ) * (f z).toReal) / θ
    have hy_epi : ((y, ry) : E × ℝ) ∈ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)} := by
      simp [ry, hy_bot]
    have hz_epi' : ((z, (f z).toReal) : E × ℝ) ∈ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)} := by
      simpa using hz_epi
    have hcombo_mem :
        θ • ((y, ry) : E × ℝ) + (1 - θ) • ((z, (f z).toReal) : E × ℝ) ∈
          {p : E × ℝ | f p.1 ≤ (p.2 : EReal)} :=
      hepigraph hy_epi hz_epi' hθ.1.le (sub_nonneg.mpr hθ.2.le) (by ring)
    have hpair :
        ((x, R) : E × ℝ) =
          θ • ((y, ry) : E × ℝ) + (1 - θ) • ((z, (f z).toReal) : E × ℝ) := by
      ext
      · simpa [ry] using hx_combo
      · dsimp [ry]
        field_simp [hθ.1.ne']
        ring_nf
    have hxR_mem : ((x, R) : E × ℝ) ∈ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)} := by
      rw [hpair]
      exact hcombo_mem
    exact hxR_mem
  have hbot : f x = ⊥ := by
    -- Since every real height lies above `f x`, the only possibility is `f x = ⊥`.
    rw [EReal.eq_bot_iff_forall_lt]
    intro R
    have hltR : (R - 1 : ℝ) < R := by linarith
    exact lt_of_le_of_lt (hbelow (R - 1)) (by exact_mod_cast hltR)
  exact hxfd.2 hbot

/-- Helper for Lemma 3.2: a right derivative of the finite-valued line restriction yields the
chapter directional derivative. -/
lemma hasDirectionalDerivativeAtOfHasDerivWithinAtIoi
    (f : E → EReal) (x d : E) (hx : x ∈ interior (finite_domain f))
    {ℓ : ℝ}
    (hd : HasDerivWithinAt (fun t : ℝ ↦ (f (x + t • d)).toReal) ℓ (Set.Ioi 0) 0) :
    has_directional_derivative_at f x d (ℓ : EReal) := by
  rw [has_directional_derivative_at]
  have hxfd : x ∈ finite_domain f := interior_subset hx
  have hdom : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), x + t • d ∈ finite_domain f := by
    -- Stay inside the finite domain along short positive steps from `x`.
    have hcont : Tendsto (fun t : ℝ ↦ x + t • d) (𝓝 (0 : ℝ)) (𝓝 x) := by
      simpa using
        tendsto_const_nhds.add
          (((tendsto_id : Tendsto (fun t : ℝ ↦ t) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ))).smul_const d))
    have hinterior :
        ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), x + t • d ∈ interior (finite_domain f) := by
      exact (hcont.eventually <| isOpen_interior.mem_nhds hx).filter_mono nhdsWithin_le_nhds
    exact hinterior.mono fun t ht ↦ interior_subset ht
  have hslope :
      Tendsto
        (fun t : ℝ ↦ ((((f (x + t • d)).toReal - (f x).toReal) / t : ℝ) : EReal))
        (𝓝[>] (0 : ℝ))
        (𝓝 ((ℓ : ℝ) : EReal)) :=
    EReal.tendsto_coe.2 <| by
      have hslopeReal :
          Tendsto (slope (fun t : ℝ ↦ (f (x + t • d)).toReal) 0) (𝓝[>] (0 : ℝ)) (𝓝 ℓ) :=
        (hasDerivWithinAt_iff_tendsto_slope' (x := (0 : ℝ)) (s := Set.Ioi 0) (by simp)).1 hd
      refine hslopeReal.congr' ?_
      have hnonzero : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t ≠ 0 := by
        refine (eventually_mem_nhdsWithin : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t ∈ Set.Ioi (0 : ℝ)).mono ?_
        intro t ht
        exact ne_of_gt ht
      filter_upwards
        [hnonzero] with t ht
      simp [slope_def_field]
  refine hslope.congr' ?_
  filter_upwards [hdom] with t ht
  have hxt : ((f (x + t • d)).toReal : EReal) = f (x + t • d) := by
    exact EReal.coe_toReal (mem_effective_domain.mp ht.1).ne ht.2
  have hx0 : ((f x).toReal : EReal) = f x := by
    exact EReal.coe_toReal (mem_effective_domain.mp hxfd.1).ne hxfd.2
  simp [hxt, hx0, EReal.coe_sub, EReal.coe_div]

/-- Lemma 3.2: at an interior point of `finite_domain f`, every `y ∈ effective_domain f`
satisfies the directional-derivative lower bound in the direction `y - x`. This is the
owner-level affine lower bound behind the source-facing `effective_domain` formulation. -/
theorem value_ge_value_add_directional_derivative_at_interior_finite_domain
    (f : E → EReal) (x y : E) (hconvex : is_convex_function f)
    (hx : x ∈ interior (finite_domain f)) (hy : y ∈ effective_domain f) :
    f y ≥ f x + directional_derivative f x (y - x) := by
  have hneBot : ∀ z : E, f z ≠ ⊥ :=
    valueNeBotOfMemInteriorFiniteDomain f x hconvex hx
  have hxfd : x ∈ finite_domain f := interior_subset hx
  have hxeff : x ∈ interior (effective_domain f) := by
    -- The no-`⊥` helper identifies the finite and effective domains near `x`.
    simpa [finite_domain_eq_effective_domain hneBot] using hx
  let line : ℝ →ᵃ[ℝ] E := AffineMap.lineMap x y
  let g : ℝ → ℝ := fun t ↦ (f (line t)).toReal
  let S : Set ℝ := {t : ℝ | line t ∈ effective_domain f}
  have hconvReal :
      ConvexOn ℝ (effective_domain f) (fun z ↦ (f z).toReal) :=
    convexOn_toReal_of_is_convex_function hconvex (fun z _ ↦ hneBot z)
  have hconvLine : ConvexOn ℝ S g := by
    -- Restrict the convex finite-valued function to the line segment from `x` to `y`.
    simpa [g, S] using hconvReal.comp_affineMap line
  have hzeroInterior : (0 : ℝ) ∈ interior S := by
    -- Pull the interior membership of `x` back along the affine line map.
    have hzeroPre : (0 : ℝ) ∈ line ⁻¹' interior (effective_domain f) := by
      simpa [line, Set.preimage, AffineMap.lineMap_apply_zero] using hxeff
    have : (0 : ℝ) ∈ interior (line ⁻¹' effective_domain f) :=
      (preimage_interior_subset_interior_preimage AffineMap.lineMap_continuous) hzeroPre
    simpa [S, Set.preimage] using this
  have hone : (1 : ℝ) ∈ S := by
    -- The endpoint `t = 1` of the line segment is exactly `y`.
    simpa [S, line] using hy
  have hderiv :
      HasDerivWithinAt g (derivWithin g (Set.Ioi 0) 0) (Set.Ioi 0) 0 :=
    hconvLine.hasDerivWithinAt_rightDeriv_of_mem_interior hzeroInterior
  have hdirHas :
      has_directional_derivative_at f x (y - x)
        ((derivWithin g (Set.Ioi 0) 0 : ℝ) : EReal) := by
    -- Convert the right derivative of the real line restriction back to the chapter definition.
    have hderivLine :
        HasDerivWithinAt (fun t : ℝ ↦ (f (x + t • (y - x))).toReal)
          (derivWithin g (Set.Ioi 0) 0) (Set.Ioi 0) 0 := by
      simpa [g, line, AffineMap.lineMap_apply_module', add_comm] using hderiv
    exact hasDirectionalDerivativeAtOfHasDerivWithinAtIoi
      f x (y - x) hx hderivLine
  have hboundReal :
      derivWithin g (Set.Ioi 0) 0 ≤ (f y).toReal - (f x).toReal := by
    -- The right derivative of a convex real function is bounded by the secant slope to `t = 1`.
    simpa [g, line, slope_def_field] using
      hconvLine.rightDeriv_le_slope_of_mem_interior hzeroInterior hone zero_lt_one
  have hyTop : f y ≠ ⊤ := ne_of_lt (mem_effective_domain.mp hy)
  have hxTop : f x ≠ ⊤ := ne_of_lt (mem_effective_domain.mp hxfd.1)
  have hdirLeSub :
      directional_derivative f x (y - x) ≤ f y - f x := by
    -- Rewrite the real secant bound in `EReal` coordinates.
    calc
      directional_derivative f x (y - x) =
          ((derivWithin g (Set.Ioi 0) 0 : ℝ) : EReal) :=
        directional_derivative_eq_of_has_directional_derivative_at hdirHas
      _ ≤ (((f y).toReal - (f x).toReal : ℝ) : EReal) := EReal.coe_le_coe hboundReal
      _ = f y - f x := by
        rw [EReal.coe_sub, EReal.coe_toReal hyTop (hneBot y), EReal.coe_toReal hxTop hxfd.2]
  have hadd :
      directional_derivative f x (y - x) + f x ≤ f y :=
    (EReal.le_sub_iff_add_le (Or.inl hxfd.2) (Or.inr hyTop)).1 hdirLeSub
  simpa [add_comm] using hadd

/-- Source-facing bridge for Lemma 3.2: if `f` is a convex extended-real-valued function that
never takes the value `-∞` and `x` lies in the interior of its effective domain, then every
`y ∈ effective_domain f` satisfies the affine lower bound determined by the directional
derivative of `f` at `x` in the direction `y - x`. This restates the owner-level
`finite_domain` formulation above under the no-`⊥` hypothesis. -/
theorem value_ge_value_add_directional_derivative_of_mem_effective_domain
    (f : E → EReal) (x y : E) (hconvex : is_convex_function f)
    (h_ne_bot : ∀ z, f z ≠ ⊥) (hx : x ∈ interior (effective_domain f))
    (hy : y ∈ effective_domain f) :
    f y ≥ f x + directional_derivative f x (y - x) := by
  simpa [finite_domain_eq_effective_domain h_ne_bot] using
    value_ge_value_add_directional_derivative_at_interior_finite_domain f x y hconvex
      (by simpa [finite_domain_eq_effective_domain h_ne_bot] using hx) hy

end

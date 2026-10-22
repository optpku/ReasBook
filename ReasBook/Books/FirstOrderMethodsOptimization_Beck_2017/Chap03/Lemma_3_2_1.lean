/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_7
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_8
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_10
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Filter
open scoped Topology

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (f : E → EReal) (x : E)

/- Lemma 3.2.1 is `source-facing` in the chapter directional-derivative API. The ambient owner
objects already live upstream: `directional_derivative` from Chapter 3 and
`is_convex_function`, together with its canonical source bridge
`is_convex_function_iff_segment_ineq`, from Chapter 2. Under the present `NormedSpace`
hypotheses the project has no stronger owner abstraction bundling convexity and positive
homogeneity of `directional_derivative f x`, so the public API stays with these two atomic
owner-level consequences instead of introducing a parallel wrapper. The primitive local hypothesis
is the chapter owner `x ∈ interior (finite_domain f)`, from which nearby finiteness is derived as
needed; the earlier split `effective_domain`/`≠ ⊥` assumptions are therefore not kept as public
data. -/
recall directional_derivative
recall has_directional_derivative_at
recall IsProperExtendedRealFunction
recall is_convex_function
recall is_convex_function_iff_segment_ineq
recall finite_domain

/-- Helper for Lemma 3.2.1: one interior finite-domain point of a convex function rules out the
value `⊥` globally. -/
theorem convexFunctionNeBotOfMemInteriorFiniteDomain
    (hconvex : is_convex_function f) (hx : x ∈ interior (finite_domain f)) :
    ∀ y : E, f y ≠ ⊥ := by
  intro y
  by_contra hy_bot
  have hxfd : x ∈ finite_domain f := interior_subset hx
  by_cases hxy : y = x
  · exact hxfd.2 (hxy ▸ hy_bot)
  obtain ⟨ε, hε_pos, hε_ball⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hx)
  let s : ℝ := min (ε / (2 * ‖y - x‖)) (1 / 2)
  have hnorm_pos : 0 < ‖y - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hs_pos : 0 < s := by
    -- Choose a small positive step so the convex combination stays inside the interior ball.
    dsimp [s]
    refine lt_min ?_ (by norm_num)
    exact div_pos hε_pos (by positivity)
  have hs_mem : s ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact le_of_lt hs_pos
    · dsimp [s]
      linarith [min_le_right (ε / (2 * ‖y - x‖)) (1 / 2 : ℝ)]
  let z : E := x + s • (y - x)
  have hz_ball : z ∈ Metric.ball x ε := by
    -- The chosen step keeps `z` within the interior ball around `x`.
    rw [Metric.mem_ball, dist_eq_norm]
    dsimp [z]
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (le_of_lt hs_pos)]
    have hs_le : s ≤ ε / (2 * ‖y - x‖) := by
      dsimp [s]
      exact min_le_left _ _
    have hs_mul : s * (2 * ‖y - x‖) ≤ ε := by
      exact (le_div_iff₀ (by positivity)).mp hs_le
    have hs_norm : s * ‖y - x‖ ≤ ε / 2 := by
      nlinarith
    linarith
  have hz_finite : z ∈ finite_domain f := interior_subset (hε_ball hz_ball)
  have hz_eq : z = s • y + (1 - s) • x := by
    -- Rewrite the affine perturbation as the convex combination used by the segment inequality.
    dsimp [z]
    calc
      x + s • (y - x) = x + (s • y - s • x) := by rw [smul_sub]
      _ = x + (s • y + -(s • x)) := by rw [sub_eq_add_neg]
      _ = x + (s • y + (-s) • x) := by
        exact congrArg (fun u ↦ x + (s • y + u)) (neg_smul s x).symm
      _ = s • y + ((-s) + 1) • x := by
        rw [add_smul, one_smul]
        abel
      _ = s • y + (1 - s) • x := by ring_nf
  let r : ℝ := (((f z).toReal - (1 - s) * (f x).toReal) / s) - 1
  have hepigraph :
      Convex ℝ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)} :=
    (is_convex_function_iff_convex_real_epigraph f).mp hconvex
  have hx_epi : (x, (f x).toReal) ∈ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)} := by
    exact EReal.le_coe_toReal (ne_of_lt (mem_effective_domain.mp hxfd.1))
  have hy_epi : (y, r) ∈ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)} := by
    -- If `f y = ⊥`, then every real height lies above it in the epigraph.
    simp [hy_bot, r]
  have hsum : s + (1 - s) = 1 := by linarith
  have hz_epi :
      (z, s * r + (1 - s) * (f x).toReal) ∈ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)} := by
    -- Convexity of the real epigraph transports the low point at `y` to the nearby point `z`.
    simpa [hz_eq] using
      (convex_iff_add_mem.mp hepigraph) hy_epi hx_epi (le_of_lt hs_pos) (sub_nonneg.mpr hs_mem.2) hsum
  have hz_upper :
      f z ≤ ((s * r + (1 - s) * (f x).toReal : ℝ) : EReal) := by
    simpa [r] using hz_epi
  have hz_height_lt :
      s * r + (1 - s) * (f x).toReal < (f z).toReal := by
    -- The chosen height is strictly below the finite value of `f z`.
    dsimp [r]
    have hs_ne : s ≠ 0 := ne_of_gt hs_pos
    field_simp [hs_ne]
    nlinarith
  have hz_top : f z ≠ ⊤ := (mem_effective_domain.mp hz_finite.1).ne
  have hz_bound_lt : ((s * r + (1 - s) * (f x).toReal : ℝ) : EReal) < f z := by
    calc
      ((s * r + (1 - s) * (f x).toReal : ℝ) : EReal) < (((f z).toReal : ℝ) : EReal) := by
        exact EReal.coe_lt_coe_iff.mpr hz_height_lt
      _ = f z := EReal.coe_toReal hz_top hz_finite.2
  exact not_lt_of_ge hz_upper hz_bound_lt

/-- Helper for Lemma 3.2.1: a convex function with an interior finite-domain point is proper. -/
theorem properExtendedRealFunctionOfConvexInteriorFiniteDomain
    (hconvex : is_convex_function f) (hx : x ∈ interior (finite_domain f)) :
    IsProperExtendedRealFunction f := by
  refine ⟨convexFunctionNeBotOfMemInteriorFiniteDomain (f := f) (x := x) hconvex hx, ?_⟩
  -- The interior finite-domain hypothesis already supplies a finite effective-domain point.
  exact ⟨x, (interior_subset hx).1⟩

/-- Helper for Lemma 3.2.1: points along a short positive ray from `x` stay in the finite domain
of `f`. -/
lemma eventuallyMemFiniteDomainAlong
    (hx : x ∈ interior (finite_domain f)) (d : E) :
    ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), x + t • d ∈ finite_domain f := by
  have hcont : Tendsto (fun t : ℝ ↦ x + t • d) (𝓝 (0 : ℝ)) (𝓝 x) := by
    simpa using
      tendsto_const_nhds.add
        (((tendsto_id : Tendsto (fun t : ℝ ↦ t) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ))).smul_const d))
  have hinterior :
      ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), x + t • d ∈ interior (finite_domain f) := by
    exact (hcont.eventually <| isOpen_interior.mem_nhds hx).filter_mono nhdsWithin_le_nhds
  -- Shrink the eventual statement from the interior to the finite domain itself.
  exact hinterior.mono fun t ht ↦ interior_subset ht

/-- Helper for Lemma 3.2.1: once the directional derivative exists with a finite real value, the
finite-valued real quotient has the same right-hand limit. -/
lemma tendstoRealDirectionalQuotientOfHasDirectionalDerivativeAt
    (hx : x ∈ interior (finite_domain f)) {d : E} {ℓ : ℝ}
    (h : has_directional_derivative_at f x d (ℓ : EReal)) :
    Tendsto (fun α : ℝ ↦ ((f (x + α • d)).toReal - (f x).toReal) / α)
      (𝓝[>] (0 : ℝ)) (𝓝 ℓ) := by
  have hxfd : x ∈ finite_domain f := interior_subset hx
  have hcoerced :
      Tendsto
        (fun α : ℝ ↦ ((((f (x + α • d)).toReal - (f x).toReal) / α : ℝ) : EReal))
        (𝓝[>] (0 : ℝ))
        (𝓝 (ℓ : EReal)) := by
    -- Near `0`, both endpoint values are finite, so the `EReal` quotient is the coerced real one.
    refine h.congr' ?_
    filter_upwards [eventuallyMemFiniteDomainAlong (f := f) (x := x) hx d] with α hα
    have hxt : ((f (x + α • d)).toReal : EReal) = f (x + α • d) := by
      exact EReal.coe_toReal (mem_effective_domain.mp hα.1).ne hα.2
    have hx0 : ((f x).toReal : EReal) = f x := by
      exact EReal.coe_toReal (mem_effective_domain.mp hxfd.1).ne hxfd.2
    simp [hxt, hx0, EReal.coe_sub, EReal.coe_div]
  exact (EReal.tendsto_coe.1 hcoerced)

/-- Helper for Lemma 3.2.1: every directional derivative at an interior finite-domain point is a
finite extended real number, so the derivative function is proper. -/
theorem directionalDerivativeIsProperExtendedRealFunction
    (hconvex : is_convex_function f) (hx : x ∈ interior (finite_domain f)) :
    IsProperExtendedRealFunction (directional_derivative f x) := by
  refine ⟨?_, ?_⟩
  · intro d
    -- The existence theorem supplies a real representative for each directional derivative.
    rcases exists_real_has_directional_derivative_at_of_convex_interior_point
      (f := f) (x := x) (d := d) hconvex hx with ⟨ℓ, hℓ⟩
    rw [directional_derivative_eq_of_has_directional_derivative_at hℓ]
    exact EReal.coe_ne_bot _
  · rcases exists_real_has_directional_derivative_at_of_convex_interior_point
      (f := f) (x := x) (d := (0 : E)) hconvex hx with ⟨ℓ, hℓ⟩
    refine ⟨0, ?_⟩
    change directional_derivative f x (0 : E) < ⊤
    rw [directional_derivative_eq_of_has_directional_derivative_at hℓ]
    exact EReal.coe_lt_top _

/-- Helper for Lemma 3.2.1: the directional derivative satisfies the segment inequality in the
direction variable. -/
lemma directionalDerivativeSegmentIneq
    (hconvex : is_convex_function f) (hx : x ∈ interior (finite_domain f))
    {d₁ d₂ : E} {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    directional_derivative f x (t • d₁ + (1 - t) • d₂) ≤
      (t : EReal) * directional_derivative f x d₁ + (1 - t : EReal) * directional_derivative f x d₂ := by
  letI : IsProperExtendedRealFunction f :=
    properExtendedRealFunctionOfConvexInteriorFiniteDomain (f := f) (x := x) hconvex hx
  let d : E := t • d₁ + (1 - t) • d₂
  let q : E → ℝ → ℝ :=
    fun v α ↦ ((f (x + α • v)).toReal - (f x).toReal) / α
  rcases exists_real_has_directional_derivative_at_of_convex_interior_point
    (f := f) (x := x) (d := d) hconvex hx with ⟨ℓ, hℓ⟩
  rcases exists_real_has_directional_derivative_at_of_convex_interior_point
    (f := f) (x := x) (d := d₁) hconvex hx with ⟨ℓ₁, hℓ₁⟩
  rcases exists_real_has_directional_derivative_at_of_convex_interior_point
    (f := f) (x := x) (d := d₂) hconvex hx with ⟨ℓ₂, hℓ₂⟩
  have hq : Tendsto (q d) (𝓝[>] (0 : ℝ)) (𝓝 ℓ) :=
    tendstoRealDirectionalQuotientOfHasDirectionalDerivativeAt (f := f) (x := x) hx hℓ
  have hq₁ : Tendsto (q d₁) (𝓝[>] (0 : ℝ)) (𝓝 ℓ₁) :=
    tendstoRealDirectionalQuotientOfHasDirectionalDerivativeAt (f := f) (x := x) hx hℓ₁
  have hq₂ : Tendsto (q d₂) (𝓝[>] (0 : ℝ)) (𝓝 ℓ₂) :=
    tendstoRealDirectionalQuotientOfHasDirectionalDerivativeAt (f := f) (x := x) hx hℓ₂
  have hxfd : x ∈ finite_domain f := interior_subset hx
  have hpos : ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), 0 < α := by
    simpa [Set.mem_Ioi] using
      (eventually_mem_nhdsWithin : ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), α ∈ Set.Ioi (0 : ℝ))
  have hpointwise :
      ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), q d α ≤ t * q d₁ α + (1 - t) * q d₂ α := by
    filter_upwards
      [eventuallyMemFiniteDomainAlong (f := f) (x := x) hx d,
        eventuallyMemFiniteDomainAlong (f := f) (x := x) hx d₁,
        eventuallyMemFiniteDomainAlong (f := f) (x := x) hx d₂, hpos] with α hd hd₁ hd₂ hα
    have hrewrite :
        t • x + t • α • d₁ + ((1 - t) • x + (1 - t) • α • d₂) = x + α • d := by
      -- Expand both sides into the same affine normal form.
      dsimp [d]
      have hsum : t + (1 - t) = 1 := by linarith
      calc
        t • x + t • α • d₁ + ((1 - t) • x + (1 - t) • α • d₂)
            = (t • x + (1 - t) • x) + ((α * t) • d₁ + (α * (1 - t)) • d₂) := by
                rw [smul_smul, smul_smul]
                rw [mul_comm t α, mul_comm (1 - t) α]
                abel
        _ = x + ((α * t) • d₁ + (α * (1 - t)) • d₂) := by
              rw [← add_smul, hsum, one_smul]
        _ = x + (α * t) • d₁ + (α * (1 - t)) • d₂ := by
              abel
        _ = x + α • (t • d₁ + (1 - t) • d₂) := by
              rw [smul_add, smul_smul, smul_smul]
              rw [mul_comm α t, mul_comm α (1 - t)]
              abel
    have hseg :
        f (x + α • d) ≤
          (t : EReal) * f (x + α • d₁) + (1 - t : EReal) * f (x + α • d₂) := by
      -- Apply convexity to the two nearby finite points along the chosen rays.
      simpa [hrewrite] using
        is_convex_function.segment_ineq (f := f) hconvex hd₁.1 hd₂.1 ht
    have hsegReal :
        (f (x + α • d)).toReal ≤
          t * (f (x + α • d₁)).toReal + (1 - t) * (f (x + α • d₂)).toReal := by
      exact EReal.coe_le_coe_iff.mp <| by
        simpa [EReal.coe_mul, EReal.coe_add,
          EReal.coe_toReal (mem_effective_domain.mp hd.1).ne hd.2,
          EReal.coe_toReal (mem_effective_domain.mp hd₁.1).ne hd₁.2,
          EReal.coe_toReal (mem_effective_domain.mp hd₂.1).ne hd₂.2] using hseg
    have hsub :
        (f (x + α • d)).toReal - (f x).toReal ≤
          t * ((f (x + α • d₁)).toReal - (f x).toReal) +
            (1 - t) * ((f (x + α • d₂)).toReal - (f x).toReal) := by
      -- Subtract the common base value `f x` from the segment inequality.
      nlinarith [hsegReal]
    have hdiv :
        ((f (x + α • d)).toReal - (f x).toReal) / α ≤
          (t * ((f (x + α • d₁)).toReal - (f x).toReal) +
              (1 - t) * ((f (x + α • d₂)).toReal - (f x).toReal)) / α := by
      exact div_le_div_of_nonneg_right hsub (le_of_lt hα)
    have hsplit :
        (t * ((f (x + α • d₁)).toReal - (f x).toReal) +
            (1 - t) * ((f (x + α • d₂)).toReal - (f x).toReal)) / α =
          t * q d₁ α + (1 - t) * q d₂ α := by
      dsimp [q]
      field_simp [ne_of_gt hα]
    simpa [q, hsplit] using hdiv
  have hright :
      Tendsto (fun α : ℝ ↦ t * q d₁ α + (1 - t) * q d₂ α)
        (𝓝[>] (0 : ℝ))
        (𝓝 (t * ℓ₁ + (1 - t) * ℓ₂)) := by
    -- The right-hand side is a continuous real combination of the two quotient limits.
    exact (tendsto_const_nhds.mul hq₁).add ((tendsto_const_nhds.mul hq₂))
  have hlim :
      ℓ ≤ t * ℓ₁ + (1 - t) * ℓ₂ :=
    le_of_tendsto_of_tendsto hq hright hpointwise
  -- Convert the real limit inequality back to the totalized directional derivative values.
  calc
    directional_derivative f x d = (ℓ : EReal) := directional_derivative_eq_of_has_directional_derivative_at hℓ
    _ ≤ ((t * ℓ₁ + (1 - t) * ℓ₂ : ℝ) : EReal) := EReal.coe_le_coe hlim
    _ = (((t * ℓ₁ : ℝ) : EReal) + (((1 - t) * ℓ₂ : ℝ) : EReal)) := by
      rw [EReal.coe_add]
    _ = (t : EReal) * (ℓ₁ : EReal) + (((1 - t : ℝ) : EReal) * (ℓ₂ : EReal)) := by
      rw [EReal.coe_mul, EReal.coe_mul]
    _ = (t : EReal) * (ℓ₁ : EReal) + (1 - t : EReal) * (ℓ₂ : EReal) := by
      rfl
    _ = (t : EReal) * directional_derivative f x d₁ + (1 - t : EReal) * directional_derivative f x d₂ := by
      rw [directional_derivative_eq_of_has_directional_derivative_at hℓ₁,
        directional_derivative_eq_of_has_directional_derivative_at hℓ₂]

/-- Helper for Lemma 3.2.1: nonnegative scalar multiplication transports a finite directional
derivative by the same scalar. -/
lemma hasDirectionalDerivativeAtNonnegSmul
    (hx : x ∈ interior (finite_domain f)) {d : E} {a ℓ : ℝ}
    (ha : 0 ≤ a) (h : has_directional_derivative_at f x d (ℓ : EReal)) :
    has_directional_derivative_at f x (a • d) ((a * ℓ : ℝ) : EReal) := by
  rw [has_directional_derivative_at]
  by_cases hzero : a = 0
  · -- Route correction: the zero-scalar branch is handled directly from the constant quotient.
    rw [hzero, zero_smul, zero_mul]
    have hxfd : x ∈ finite_domain f := interior_subset hx
    have hx0 : f x = ((f x).toReal : EReal) := by
      symm
      exact EReal.coe_toReal (mem_effective_domain.mp hxfd.1).ne hxfd.2
    have hsub : f x - f x = (0 : EReal) := by
      rw [hx0]
      simp
    have hconst :
        (fun α : ℝ ↦ (f (x + α • (0 : E)) - f x) / (α : EReal)) = fun _ ↦ (0 : EReal) := by
      funext α
      simp [hsub]
    rw [hconst]
    exact tendsto_const_nhds
  · have ha_ne : 0 ≠ a := by simpa [eq_comm] using hzero
    have ha_pos : 0 < a := lt_of_le_of_ne ha ha_ne
    let q : ℝ → ℝ := fun β ↦ ((f (x + β • d)).toReal - (f x).toReal) / β
    have hq : Tendsto q (𝓝[>] (0 : ℝ)) (𝓝 ℓ) :=
      tendstoRealDirectionalQuotientOfHasDirectionalDerivativeAt (f := f) (x := x) hx h
    have hmap :
        Tendsto (fun α : ℝ ↦ α * a) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
      simpa using Filter.TendstoNhdsWithinIoi.mul_const (b := a) (c := (0 : ℝ))
        (f := fun α : ℝ ↦ α) (l := 𝓝[>] (0 : ℝ)) ha_pos tendsto_id
    have hpos : ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), 0 < α := by
      simpa [Set.mem_Ioi] using
        (eventually_mem_nhdsWithin : ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), α ∈ Set.Ioi (0 : ℝ))
    have hrewriteReal :
        ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ),
          ((f (x + α • (a • d))).toReal - (f x).toReal) / α = a * q (α * a) := by
      filter_upwards [hpos] with α hα
      have hαne : α ≠ 0 := ne_of_gt hα
      have ha_ne : a ≠ 0 := ne_of_gt ha_pos
      dsimp [q]
      rw [smul_smul, mul_comm]
      field_simp [hαne, ha_ne]
    have hreal :
        Tendsto (fun α : ℝ ↦ ((f (x + α • (a • d))).toReal - (f x).toReal) / α)
          (𝓝[>] (0 : ℝ))
          (𝓝 (a * ℓ)) := by
      -- Reparameterize the original real quotient by `α ↦ α * a`.
      exact ((tendsto_const_nhds.mul (hq.comp hmap))).congr' <|
        hrewriteReal.mono fun α hα ↦ hα.symm
    have hxfd : x ∈ finite_domain f := interior_subset hx
    have hcoerced :
        Tendsto
          (fun α : ℝ ↦
            ((((f (x + α • (a • d))).toReal - (f x).toReal) / α : ℝ) : EReal))
          (𝓝[>] (0 : ℝ))
          (𝓝 ((a * ℓ : ℝ) : EReal)) :=
      EReal.tendsto_coe.2 hreal
    have hdom :
        ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), x + α • (a • d) ∈ finite_domain f :=
      eventuallyMemFiniteDomainAlong (f := f) (x := x) hx (a • d)
    -- Near `0`, the `EReal` quotient in direction `a • d` is the coerced real quotient above.
    exact hcoerced.congr' <| by
      filter_upwards [hdom] with α hα
      have hxt : ((f (x + α • (a • d))).toReal : EReal) = f (x + α • (a • d)) := by
        exact EReal.coe_toReal (mem_effective_domain.mp hα.1).ne hα.2
      have hx0 : ((f x).toReal : EReal) = f x := by
        exact EReal.coe_toReal (mem_effective_domain.mp hxfd.1).ne hxfd.2
      simp [hxt, hx0, EReal.coe_sub, EReal.coe_div]

-- Proof sketch: apply the chapter owner characterization of convexity from
-- `is_convex_function_iff_segment_ineq` to the function `d ↦ directional_derivative f x d`. For
-- `t ∈ [0, 1]`, compare the directional difference quotient in the mixed direction
-- `t • d₁ + (1 - t) • d₂` with the corresponding convex combination of the quotients in the
-- directions `d₁` and `d₂` using convexity of `f`, then pass to the right-hand limit. The
-- hypothesis `hx` already supplies the local finite-valued neighborhood needed to keep those
-- quotients meaningful near `0`.
/-- Lemma 3.2.1 (1): for a convex extended-real-valued function and an interior point of its finite
domain, the directional derivative is a convex extended-real-valued function of the direction. -/
theorem directional_derivative_is_convex_function
    (hconvex : is_convex_function f) (hx : x ∈ interior (finite_domain f)) :
    is_convex_function (directional_derivative f x) := by
  letI : IsProperExtendedRealFunction (directional_derivative f x) :=
    directionalDerivativeIsProperExtendedRealFunction (f := f) (x := x) hconvex hx
  rw [is_convex_function_iff_segment_ineq]
  intro d₁ _ d₂ _ t ht
  -- The local segment inequality proved above is exactly the convexity API endpoint.
  exact directionalDerivativeSegmentIneq (f := f) (x := x) hconvex hx ht

-- Proof sketch: if `a = 0`, compute directly from the difference quotient. For `a > 0`, rewrite
-- the quotient in direction `a • d` by the change of variables `β = α * a`, factor out the scalar
-- `(a : EReal)`, and pass to the right-hand limit defining `directional_derivative`.
/-- Lemma 3.2.1 (2): for a convex extended-real-valued function and an interior point of its finite
domain, the directional derivative is positively homogeneous in the direction variable. -/
theorem directional_derivative_nonneg_smul
    (hconvex : is_convex_function f) (hx : x ∈ interior (finite_domain f))
    (a : ℝ) (ha : 0 ≤ a) (d : E) :
    directional_derivative f x (a • d) = (a : EReal) * directional_derivative f x d := by
  rcases exists_real_has_directional_derivative_at_of_convex_interior_point
    (f := f) (x := x) (d := d) hconvex hx with ⟨ℓ, hℓ⟩
  have hscaled :
      has_directional_derivative_at f x (a • d) ((a * ℓ : ℝ) : EReal) :=
    hasDirectionalDerivativeAtNonnegSmul (f := f) (x := x) hx ha hℓ
  -- Identify both directional derivatives with the real witnesses given by the existence theorem.
  calc
    directional_derivative f x (a • d) = ((a * ℓ : ℝ) : EReal) :=
      directional_derivative_eq_of_has_directional_derivative_at hscaled
    _ = (a : EReal) * directional_derivative f x d := by
      rw [directional_derivative_eq_of_has_directional_derivative_at hℓ, EReal.coe_mul]

end

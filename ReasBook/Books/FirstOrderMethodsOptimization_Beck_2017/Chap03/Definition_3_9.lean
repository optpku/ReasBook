/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_2
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_8
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_10
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_3
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_8
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Lemma_3_2
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Lemma_3_2_1
import Mathlib.Analysis.Convex.Cone.Extension

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Filter
open scoped Topology

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-
Textbook context: the max formula reuses `directional_derivative f x d` from Definition 3.8
together with the owner set `∂ f(x)`, presenting `f'(x; d)` as the maximum of the pairing image
`(fun g : Module.Dual ℝ E ↦ (g d : EReal)) '' ∂ f(x)`.
-/
recall IsProperExtendedRealFunction
recall directional_derivative
recall subdifferential
recall finite_domain
recall subdifferential_nonempty_at_interior_point
recall value_ge_value_add_directional_derivative_of_mem_effective_domain
recall directional_derivative_nonneg_smul
recall directionalDerivativeSegmentIneq

omit [FiniteDimensional ℝ E] in
/-- Helper for Definition 3.9: at an interior effective-domain point of a proper convex function,
every directional derivative is represented by a real number. -/
lemma directionalDerivative_eq_coe_toReal_at_interior_point
    {f : E → EReal} [IsProperExtendedRealFunction f] {x v : E}
    (hconvex : is_convex_function f) (hx : x ∈ interior (effective_domain f)) :
    directional_derivative f x v = ((directional_derivative f x v).toReal : EReal) := by
  let h_ne_bot : ∀ y, f y ≠ ⊥ := IsProperExtendedRealFunction.ne_bot
  have hxFinite : x ∈ interior (finite_domain f) := by
    simpa [finite_domain_eq_effective_domain h_ne_bot] using hx
  -- The Chapter 3 existence theorem identifies the directional derivative with a finite real limit.
  rcases exists_real_has_directional_derivative_at_of_convex_interior_point
      f x v hconvex hxFinite with
    ⟨ℓ, hℓ⟩
  rw [directional_derivative_eq_of_has_directional_derivative_at hℓ]
  simp

omit [FiniteDimensional ℝ E] in
/-- Helper for Definition 3.9: the real-valued directional derivative is subadditive in the
direction variable. -/
lemma directionalDerivativeToReal_add_le_at_interior_point
    {f : E → EReal} [IsProperExtendedRealFunction f] {x u v : E}
    (hconvex : is_convex_function f) (hx : x ∈ interior (effective_domain f)) :
    (directional_derivative f x (u + v)).toReal ≤
      (directional_derivative f x u).toReal + (directional_derivative f x v).toReal := by
  let h_ne_bot : ∀ y, f y ≠ ⊥ := IsProperExtendedRealFunction.ne_bot
  have hxFinite : x ∈ interior (finite_domain f) := by
    simpa [finite_domain_eq_effective_domain h_ne_bot] using hx
  letI : IsProperExtendedRealFunction (directional_derivative f x) :=
    directionalDerivativeIsProperExtendedRealFunction f x hconvex hxFinite
  have hconv_toReal :
      ConvexOn ℝ (effective_domain (directional_derivative f x))
        (fun w : E ↦ (directional_derivative f x w).toReal) :=
    convexOn_toReal_of_is_convex_function_of_proper
      (directional_derivative f x)
      (directional_derivative_is_convex_function f x hconvex hxFinite)
  have hu_dom : u ∈ effective_domain (directional_derivative f x) := by
    refine mem_effective_domain.mpr ?_
    rw [directionalDerivative_eq_coe_toReal_at_interior_point hconvex hx]
    exact EReal.coe_lt_top _
  have hv_dom : v ∈ effective_domain (directional_derivative f x) := by
    refine mem_effective_domain.mpr ?_
    rw [directionalDerivative_eq_coe_toReal_at_interior_point hconvex hx]
    exact EReal.coe_lt_top _
  have hmid :
      (directional_derivative f x ((1 / 2 : ℝ) • u + (1 / 2 : ℝ) • v)).toReal ≤
        (1 / 2 : ℝ) * (directional_derivative f x u).toReal +
          (1 / 2 : ℝ) * (directional_derivative f x v).toReal := by
    simpa using
      hconv_toReal.2 hu_dom hv_dom (by norm_num) (by norm_num) (by ring)
  have hscale :
      (directional_derivative f x (u + v)).toReal =
        2 * (directional_derivative f x ((1 / 2 : ℝ) • u + (1 / 2 : ℝ) • v)).toReal := by
    simpa [smul_add, smul_smul, EReal.toReal_mul, add_comm, add_left_comm, add_assoc] using
      congrArg EReal.toReal
        (directional_derivative_nonneg_smul
          f x hconvex hxFinite 2 (by norm_num) ((1 / 2 : ℝ) • u + (1 / 2 : ℝ) • v))
  linarith

omit [FiniteDimensional ℝ E] in
/-- Helper for Definition 3.9: the real-valued function
`v ↦ (directional_derivative f x v).toReal` satisfies the sublinear hypotheses needed for
Hahn-Banach. -/
lemma directionalDerivativeToRealSublinear
    {f : E → EReal} [IsProperExtendedRealFunction f] {x : E}
    (hconvex : is_convex_function f) (hx : x ∈ interior (effective_domain f)) :
    (∀ a : ℝ, 0 < a → ∀ v : E,
        (directional_derivative f x (a • v)).toReal =
          a * (directional_derivative f x v).toReal) ∧
      ∀ u v : E,
        (directional_derivative f x (u + v)).toReal ≤
          (directional_derivative f x u).toReal + (directional_derivative f x v).toReal := by
  let h_ne_bot : ∀ y, f y ≠ ⊥ := IsProperExtendedRealFunction.ne_bot
  have hxFinite : x ∈ interior (finite_domain f) := by
    simpa [finite_domain_eq_effective_domain h_ne_bot] using hx
  refine ⟨?_, ?_⟩
  · intro a ha v
    -- Read the `EReal` homogeneity theorem through `toReal`.
    simpa [EReal.toReal_mul] using
      congrArg EReal.toReal
        (directional_derivative_nonneg_smul f x hconvex hxFinite a ha.le v)
  · intro u v
    exact directionalDerivativeToReal_add_le_at_interior_point hconvex hx

omit [FiniteDimensional ℝ E] in
/-- Helper for Definition 3.9: Hahn-Banach provides a dominated linear functional that attains the
directional derivative in any nonzero direction. -/
lemma existsDominatedLinearFunctional_eqDirectionalDerivative
    {f : E → EReal} [IsProperExtendedRealFunction f] {x d : E}
    (hconvex : is_convex_function f) (hx : x ∈ interior (effective_domain f)) (hd : d ≠ 0) :
    ∃ g : Module.Dual ℝ E,
      (∀ v : E, g v ≤ (directional_derivative f x v).toReal) ∧
        ((g d : ℝ) : EReal) = directional_derivative f x d := by
  let N : E → ℝ := fun v ↦ (directional_derivative f x v).toReal
  obtain ⟨hN_hom, hN_add⟩ := directionalDerivativeToRealSublinear hconvex hx
  let fspan : E →ₗ.[ℝ] ℝ := LinearPMap.mkSpanSingleton d (N d) hd
  have hN_zero : N (0 : E) = 0 := by
    -- The zero-direction quotient is constantly zero.
    have hzero :
        directional_derivative f x (0 : E) = (0 : EReal) := by
      simpa using
        directional_derivative_nonneg_smul
          f x hconvex
          (by
            let h_ne_bot : ∀ y, f y ≠ ⊥ := IsProperExtendedRealFunction.ne_bot
            simpa [finite_domain_eq_effective_domain h_ne_bot] using hx)
          0 (by positivity) d
    simp [N, hzero]
  have hf_le : ∀ z : fspan.domain, fspan z ≤ N z := by
    intro z
    rcases Submodule.mem_span_singleton.mp z.2 with ⟨c, hc⟩
    have hspan : c • d ∈ fspan.domain := by
      simpa [fspan] using
        Submodule.smul_mem (ℝ ∙ d) c (Submodule.mem_span_singleton_self d)
    let ddom : fspan.domain := ⟨d, by simp [fspan]⟩
    have hz_subtype : z = ⟨c • d, hspan⟩ := by
      apply Subtype.ext
      exact hc.symm
    have happly : fspan ⟨c • d, hspan⟩ = c * N d := by
      calc
        fspan ⟨c • d, hspan⟩ = fspan (c • ddom) := by rfl
        _ = c • fspan ddom := by rw [LinearPMap.map_smul]
        _ = c * N d := by
          rw [LinearPMap.mkSpanSingleton_apply ℝ ℝ hd (N d)]
          simp [smul_eq_mul]
    by_cases hc_nonneg : 0 ≤ c
    · rcases eq_or_lt_of_le hc_nonneg with rfl | hc_pos
      · -- The zero multiple is the zero element of the span.
        have hEq : fspan z = N z := by
          rw [hz_subtype, happly]
          simp [hN_zero]
        exact hEq.le
      · -- Positive multiples are exactly the homogeneous branch of the sublinear majorant.
        have hEq : fspan z = N z := by
          calc
            fspan z = c * N d := by rw [hz_subtype]; exact happly
            _ = N (c • d) := by
              symm
              exact hN_hom c hc_pos d
            _ = N z := by simp [hc]
        exact hEq.le
    · have hc_neg : c < 0 := lt_of_not_ge hc_nonneg
      have hsub :
          N (0 : E) ≤ N (c • d) + N ((-c) • d) := by
        simpa using
          hN_add (c • d) ((-c) • d)
      have hneg_hom : N ((-c) • d) = (-c) * N d :=
        hN_hom (-c) (neg_pos.mpr hc_neg) d
      have hzero_le : 0 ≤ N (c • d) + (-c) * N d := by
        rw [hN_zero, hneg_hom] at hsub
        exact hsub
      have hle : c * N d ≤ N (c • d) := by
        linarith
      calc
        fspan z = c * N d := by rw [hz_subtype]; exact happly
        _ ≤ N (c • d) := hle
        _ = N z := by simp [hc]
  obtain ⟨g, hg_ext, hg_le⟩ := exists_extension_of_le_sublinear fspan N hN_hom hN_add hf_le
  have hgd : g d = N d := by
    let ddom : fspan.domain := ⟨d, by simp [fspan]⟩
    have hgd' := hg_ext ddom
    rw [LinearPMap.mkSpanSingleton_apply ℝ ℝ hd (N d)] at hgd'
    simpa using hgd'
  refine ⟨g, hg_le, ?_⟩
  -- Rewrite the attained real value back to the `EReal` directional derivative.
  calc
    ((g d : ℝ) : EReal) = ((N d : ℝ) : EReal) := by
      simpa using congrArg (fun t : ℝ ↦ (t : EReal)) hgd
    _ = directional_derivative f x d := by
      simpa [N] using
        (directionalDerivative_eq_coe_toReal_at_interior_point hconvex hx).symm

omit [FiniteDimensional ℝ E] in
/-- Helper for Definition 3.9: any linear functional dominated by the real-valued directional
derivative belongs to the subdifferential. -/
lemma dominatedLinearFunctional_memSubdifferential
    {f : E → EReal} [IsProperExtendedRealFunction f] {x : E}
    (hconvex : is_convex_function f) (hx : x ∈ interior (effective_domain f))
    {g : Module.Dual ℝ E}
    (hg_dom : ∀ v : E, g v ≤ (directional_derivative f x v).toReal) :
    g ∈ ∂f(x) := by
  let h_ne_bot : ∀ y, f y ≠ ⊥ := IsProperExtendedRealFunction.ne_bot
  -- Rewrite subdifferential membership to the domain-restricted affine support inequality.
  rw [mem_subdifferential, is_subgradient_at_iff_forall_mem_effective_domain]
  refine ⟨interior_subset hx, ?_⟩
  intro y hy
  have hpair :
      (g (y - x) : EReal) ≤ directional_derivative f x (y - x) := by
    rw [directionalDerivative_eq_coe_toReal_at_interior_point hconvex hx]
    exact EReal.coe_le_coe (hg_dom (y - x))
  have hsupport :
      f y ≥ f x + directional_derivative f x (y - x) :=
    value_ge_value_add_directional_derivative_of_mem_effective_domain
      f x y hconvex h_ne_bot hx hy
  -- Compare the dominated linear functional to the owner directional-derivative support bound.
  have hsum :
      f x + (g (y - x) : EReal) ≤ f x + directional_derivative f x (y - x) := by
    simpa [add_comm] using add_le_add_left hpair (f x)
  exact le_trans hsum (by simpa [ge_iff_le] using hsupport)

omit [FiniteDimensional ℝ E] in
/-- Helper for Definition 3.9: every subgradient pairing is bounded above by the directional
derivative. -/
lemma subgradientPairing_leDirectionalDerivative
    {f : E → EReal} [IsProperExtendedRealFunction f] {x d : E}
    (hconvex : is_convex_function f) (hx : x ∈ interior (effective_domain f))
    {g : Module.Dual ℝ E} (hg : g ∈ ∂f(x)) :
    (g d : EReal) ≤ directional_derivative f x d := by
  let h_ne_bot : ∀ y, f y ≠ ⊥ := IsProperExtendedRealFunction.ne_bot
  have hxFinite : x ∈ interior (finite_domain f) := by
    simpa [finite_domain_eq_effective_domain h_ne_bot] using hx
  rcases exists_real_has_directional_derivative_at_of_convex_interior_point
      f x d hconvex hxFinite with
    ⟨ℓ, hℓ⟩
  have hquot :
      Tendsto (fun α : ℝ ↦ (f (x + α • d) - f x) / (α : EReal))
        (𝓝[>] (0 : ℝ)) (𝓝 ((ℓ : ℝ) : EReal)) := hℓ
  have hdom :
      ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), x + α • d ∈ effective_domain f := by
    simpa [finite_domain_eq_effective_domain h_ne_bot] using
      eventuallyMemFiniteDomainAlong f x hxFinite d
  have hpos :
      ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), 0 < α := by
    simpa [Set.mem_Ioi] using
      (eventually_mem_nhdsWithin :
        ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), α ∈ Set.Ioi (0 : ℝ))
  rw [mem_subdifferential, is_subgradient_at_iff_forall_mem_effective_domain] at hg
  have hpointwise :
      ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ),
        (g d : EReal) ≤ (f (x + α • d) - f x) / (α : EReal) := by
    filter_upwards [hdom, hpos] with α hαdom hαpos
    have hsub :
        f x + (((α * g d : ℝ) : EReal)) ≤ f (x + α • d) := by
      simpa [map_smul, smul_eq_mul, ge_iff_le, add_comm, add_left_comm, add_assoc] using
        hg.2 (x + α • d) hαdom
    have hx_top : f x ≠ ⊤ := (mem_effective_domain.mp (interior_subset hx)).ne
    have hmule :
        (((α * g d : ℝ) : EReal)) ≤ f (x + α • d) - f x := by
      exact
        (EReal.le_sub_iff_add_le (Or.inl (h_ne_bot x)) (Or.inl hx_top)).2
          (by simpa [add_comm] using hsub)
    have hαE_pos : (0 : EReal) < (α : EReal) := by
      exact_mod_cast hαpos
    have hdiv :
        (g d : EReal) ≤ (f (x + α • d) - f x) / (α : EReal) := by
      rw [EReal.le_div_iff_mul_le hαE_pos (EReal.coe_ne_top α)]
      simpa [EReal.coe_mul, mul_comm] using hmule
    exact hdiv
  have hle :
      (g d : EReal) ≤ ((ℓ : ℝ) : EReal) :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hquot hpointwise
  calc
    (g d : EReal) ≤ ((ℓ : ℝ) : EReal) := hle
    _ = directional_derivative f x d := by
      symm
      exact directional_derivative_eq_of_has_directional_derivative_at hℓ

/-- Definition 3.9: for a proper convex extended-real-valued function, the directional derivative
at an interior point of the effective domain is the maximum of the subgradient pairings `g d` over
all `g ∈ ∂f(x)`, expressed as an `IsGreatest` statement on the image of `∂f(x)` under
`g ↦ g d`. -/
theorem directional_derivative_isGreatest_subgradient_pairings_at_interior_point
    {f : E → EReal} [IsProperExtendedRealFunction f] {x d : E}
    (hconvex : is_convex_function f)
    (hx : x ∈ interior (effective_domain f)) :
    IsGreatest ((fun g : Module.Dual ℝ E ↦ (g d : EReal)) '' ∂f(x))
      (directional_derivative f x d) := by
  by_cases hd : d = 0
  · have hdd0 : directional_derivative f x d = 0 := by
      rw [hd]
      simpa using
        directional_derivative_nonneg_smul
          f x hconvex
          (by
            let h_ne_bot : ∀ y, f y ≠ ⊥ := IsProperExtendedRealFunction.ne_bot
            simpa [finite_domain_eq_effective_domain h_ne_bot] using hx)
          0 (by positivity) (0 : E)
    have hdd0' : directional_derivative f x 0 = 0 := by
      simpa [hd] using hdd0
    rcases subdifferential_nonempty_at_interior_point f x hconvex hx with ⟨g, hg⟩
    -- In the zero-direction branch, every pairing is exactly `0`, so the image has
    -- greatest element `0`.
    refine ⟨?_, ?_⟩
    · refine ⟨g, hg, ?_⟩
      rw [hd, hdd0']
      simp
    · intro y hy
      rcases hy with ⟨g', hg', rfl⟩
      rw [hd, hdd0']
      simp
  · rcases existsDominatedLinearFunctional_eqDirectionalDerivative
      hconvex hx hd with
      ⟨g, hg_dom, hgd⟩
    have hg_sub : g ∈ ∂f(x) :=
      dominatedLinearFunctional_memSubdifferential hconvex hx hg_dom
    -- The Hahn-Banach witness attains the claimed value, and the limit argument bounds every
    -- other subgradient pairing from above by the same directional derivative.
    refine ⟨⟨g, hg_sub, hgd⟩, ?_⟩
    intro y hy
    rcases hy with ⟨g', hg', rfl⟩
    exact subgradientPairing_leDirectionalDerivative hconvex hx hg'

/-- Every subgradient pairing at an interior effective-domain point is bounded above by the
directional derivative from Definition 3.9. -/
theorem subgradient_pairing_le_directional_derivative_at_interior_point
    {f : E → EReal} [IsProperExtendedRealFunction f] {x d : E}
    (hconvex : is_convex_function f) (hx : x ∈ interior (effective_domain f))
    {g : Module.Dual ℝ E} (hg : g ∈ ∂f(x)) :
    (g d : EReal) ≤ directional_derivative f x d := by
  exact
    (directional_derivative_isGreatest_subgradient_pairings_at_interior_point
      hconvex hx).2 ⟨g, hg, rfl⟩

/-- The maximum in Definition 3.9 is attained by a subgradient in `∂f(x)`. -/
theorem exists_subgradient_pairing_eq_directional_derivative_at_interior_point
    {f : E → EReal} [IsProperExtendedRealFunction f] {x d : E}
    (hconvex : is_convex_function f) (hx : x ∈ interior (effective_domain f)) :
    ∃ g ∈ ∂f(x), (g d : EReal) = directional_derivative f x d := by
  rcases
      (directional_derivative_isGreatest_subgradient_pairings_at_interior_point
        hconvex hx).1 with ⟨g, hg, hg_eq⟩
  exact ⟨g, hg, hg_eq⟩

end

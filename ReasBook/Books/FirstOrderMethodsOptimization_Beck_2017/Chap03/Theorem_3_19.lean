/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_2
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_9
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_10

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {V : Type u} {E : Type v}
variable [AddCommGroup V] [Module ℝ V]
variable [AddCommGroup E] [Module ℝ E]

/- Theorem 3.19 is `source-facing` at the chapter owner
`subdifferential : Set (Module.Dual ℝ E)`, while the ambient affine geometry already has the
canonical owner abstraction `AffineMap`. The pullback acts on subgradients through the linear part
`φ.linear.dualMap`, so the public theorem stays at the algebraic-dual owner level and downstream
`StrongDual` and Euclidean files should reuse it through the chapter bridge/view APIs rather than
repackaging the affine map as primitive data `(A, b)`. -/

recall subdifferential

-- Proof sketch: if `g ∈ ∂ f(φ x)`, then `φ x ∈ effective_domain f` and the defining
-- subgradient inequality for `g` applied to `φ y` gives
-- `f (φ y) ≥ f (φ x) + g (φ.linear (y - x))`. Rewrite the last term as
-- `(φ.linear.dualMap g) (y - x)` using `φ.linearMap_vsub` to obtain the subgradient inequality
-- for `φ.linear.dualMap g` at `x`.
/-- Helper for Theorem 3.19: weak affine transformation rule of subdifferential calculus. For
`h = f ∘ φ`, every subgradient of `f` at `φ x` pulls back along the linear part of `φ` to a
subgradient of `h` at `x`; the convex/proper standing assumptions from the textbook setting are
not needed for this owner-level inclusion statement itself. Specializing to `φ y = A y + b`
recovers the textbook notation `Aᵀ (∂ f(A x + b)) ⊆ ∂ h(x)`. -/
theorem subdifferential_precompose_affineMap_subset
    (f : E → EReal) (φ : V →ᵃ[ℝ] E) (x : V) :
    φ.linear.dualMap '' ∂ f(φ x) ⊆
      ∂ (fun y ↦ f (φ y))(x) := by
  intro g hg
  rcases hg with ⟨d, hd, rfl⟩
  rw [mem_subdifferential] at hd ⊢
  -- Pull the effective-domain condition back through the affine map.
  refine ⟨by simpa [effective_domain] using hd.1, ?_⟩
  intro y
  -- Reindex the supporting inequality along the affine image `φ y`.
  have hineq := hd.2 (φ y)
  have hrewrite :
      (d (φ y - φ x) : EReal) = (d (φ.linear (y - x)) : EReal) := by
    exact congrArg (fun z : ℝ ↦ (z : EReal))
      (congrArg d (φ.linearMap_vsub y x).symm)
  rw [hrewrite] at hineq
  simpa [LinearMap.dualMap_apply] using hineq

end

section

variable {V : Type u} {E : Type v}
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

recall finite_domain

omit [FiniteDimensional ℝ V] in
/-- Helper for Theorem 3.19: affine precomposition pulls the finite domain back by set preimage. -/
@[simp] lemma finite_domain_precompose_affineMap_eq_preimage
    (f : E → EReal) (φ : V →ᵃ[ℝ] E) :
    finite_domain (fun y ↦ f (φ y)) = φ ⁻¹' finite_domain f := by
  ext y
  simp [finite_domain, effective_domain]

/-- Helper for Theorem 3.19: interior finite-domain membership pulls back along affine
precomposition. -/
lemma mem_interior_finiteDomain_precompose_affineMap
    (f : E → EReal) (φ : V →ᵃ[ℝ] E) (x : V)
    (hφx : φ x ∈ interior (finite_domain f)) :
    x ∈ interior (finite_domain (fun y ↦ f (φ y))) := by
  -- Pull the open interior neighborhood back through the continuous affine map.
  have hpre : x ∈ φ ⁻¹' interior (finite_domain f) := hφx
  have hpull :
      x ∈ interior (φ ⁻¹' finite_domain f) :=
    preimage_interior_subset_interior_preimage
      (AffineMap.continuous_of_finiteDimensional φ) hpre
  simpa [finite_domain_precompose_affineMap_eq_preimage] using hpull

end

section

variable {V : Type u} {E : Type v}
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

recall finite_domain

/-- Helper for Theorem 3.19: directional derivatives commute with affine precomposition after
transporting the direction through the linear part. -/
lemma directional_derivative_precompose_affineMap
    (f : E → EReal) (φ : V →ᵃ[ℝ] E) (x d : V) :
    directional_derivative (fun y ↦ f (φ y)) x d =
      directional_derivative f (φ x) (φ.linear d) := by
  -- Normalize the difference quotient pointwise before taking the common right limit.
  unfold directional_derivative
  congr with α
  have hmap : φ (x + α • d) = φ x + α • φ.linear d := by
    rw [show x + α • d = (α • d) +ᵥ x by simp [vadd_eq_add, add_comm]]
    simpa [vadd_eq_add, add_comm] using φ.map_vadd x (α • d)
  simp [hmap]

end

section

variable {V : Type u} {E : Type v}
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

recall finite_domain

/-- Helper for Theorem 3.19: a subgradient of `f ∘ φ` at `x` annihilates the kernel of the linear
part of `φ`. -/
lemma subgradient_precompose_affineMap_mem_dualAnnihilator
    (f : E → EReal) (φ : V →ᵃ[ℝ] E) (x : V)
    (hconvex : is_convex_function f)
    (hφx : φ x ∈ interior (finite_domain f))
    {g : Module.Dual ℝ V}
    (hg : g ∈ ∂(fun y ↦ f (φ y))(x)) :
    g ∈ φ.linear.ker.dualAnnihilator := by
  let h : V → EReal := fun y ↦ f (φ y)
  let hconvex_pre : is_convex_function h :=
    is_convex_function_precompose_affineMap hconvex φ
  have hx_pre :
      x ∈ interior (finite_domain h) :=
    mem_interior_finiteDomain_precompose_affineMap f φ x hφx
  letI : IsProperExtendedRealFunction h :=
    properExtendedRealFunctionOfConvexInteriorFiniteDomain
      h x hconvex_pre hx_pre
  have hne_bot : ∀ y ∈ effective_domain h, h y ≠ ⊥ := fun y _ ↦
    IsProperExtendedRealFunction.ne_bot y
  rw [Submodule.mem_dualAnnihilator]
  intro k hk
  rw [mem_subdifferential] at hg
  have hx_dom : x ∈ effective_domain h := hg.1
  have hk_plus_value : h (x + k) = h x := by
    -- Along the kernel fiber, the affine map has the same image.
    have hker : φ.linear k = 0 := by
      simpa using hk
    have hmap : φ (x + k) = φ x := by
      rw [show x + k = k +ᵥ x by simp [vadd_eq_add, add_comm]]
      simpa [vadd_eq_add, hker] using φ.map_vadd x k
    exact congrArg f hmap
  have hk_minus_value : h (x - k) = h x := by
    -- The same fiber argument applies to the opposite direction.
    have hker : φ.linear k = 0 := by
      simpa using hk
    have hmap : φ (x - k) = φ x := by
      rw [show x - k = (-k) +ᵥ x by simp [vadd_eq_add, sub_eq_add_neg, add_comm]]
      simpa [vadd_eq_add, hker] using φ.map_vadd x (-k)
    exact congrArg f hmap
  have hk_plus_dom : x + k ∈ effective_domain h := by
    simpa [hk_plus_value] using hx_dom
  have hk_minus_dom : x - k ∈ effective_domain h := by
    simpa [hk_minus_value] using hx_dom
  have hplus : g k ≤ 0 := by
    have hsub :=
      subgradient_eval_le_toReal_sub h x (x + k) hne_bot hx_dom hk_plus_dom hg
    simpa [h, hk_plus_value] using hsub
  have hminus : -g k ≤ 0 := by
    have hsub :=
      subgradient_eval_le_toReal_sub h x (x - k) hne_bot hx_dom hk_minus_dom hg
    have hneg : g (-k) ≤ 0 := by
      simpa [h, hk_minus_value] using hsub
    simpa [map_neg] using hneg
  linarith

end

section

variable {V : Type u} {E : Type v}
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

recall finite_domain

omit [FiniteDimensional ℝ E] in
/-- Helper for Theorem 3.19: every subgradient of `f ∘ φ` is pointwise dominated by the
directional derivative of `f` along the transported direction. -/
lemma subgradient_precompose_affineMap_le_targetDirectionalDerivative
    (f : E → EReal) (φ : V →ᵃ[ℝ] E) (x : V)
    (hconvex : is_convex_function f)
    (hφx : φ x ∈ interior (finite_domain f))
    {g : Module.Dual ℝ V}
    (hg : g ∈ ∂(fun y ↦ f (φ y))(x)) (v : V) :
    g v ≤ (directional_derivative f (φ x) (φ.linear v)).toReal := by
  let h : V → EReal := fun y ↦ f (φ y)
  let hconvex_pre : is_convex_function h :=
    is_convex_function_precompose_affineMap hconvex φ
  have hx_pre :
      x ∈ interior (finite_domain h) :=
    mem_interior_finiteDomain_precompose_affineMap f φ x hφx
  letI : IsProperExtendedRealFunction h :=
    properExtendedRealFunctionOfConvexInteriorFiniteDomain
      h x hconvex_pre hx_pre
  letI : IsProperExtendedRealFunction f :=
    properExtendedRealFunctionOfConvexInteriorFiniteDomain
      f (φ x) hconvex hφx
  have hx_pre_effective : x ∈ interior (effective_domain h) := by
    simpa [finite_domain_eq_effective_domain IsProperExtendedRealFunction.ne_bot]
      using hx_pre
  have hφx_effective : φ x ∈ interior (effective_domain f) := by
    simpa [finite_domain_eq_effective_domain IsProperExtendedRealFunction.ne_bot]
      using hφx
  have hpair :
      (g v : EReal) ≤ directional_derivative h x v :=
    subgradientPairing_leDirectionalDerivative
      hconvex_pre hx_pre_effective hg
  -- Rewrite the pullback directional derivative into the target derivative of `f`.
  rw [directional_derivative_precompose_affineMap] at hpair
  rw [directionalDerivative_eq_coe_toReal_at_interior_point
    hconvex hφx_effective] at hpair
  exact_mod_cast hpair

-- Proof sketch: combine the weak inclusion with the max formula for directional derivatives at
-- interior finite-domain points. For every direction `d`, compare the support functions of the
-- two convex sets `∂ (fun y ↦ f (φ y))(x)` and `φ.linear.dualMap '' ∂ f(φ x)` via the identity
-- `h' (x; d) = f' (φ x; φ.linear d)`. The hypothesis `φ x ∈ interior (finite_domain f)` is the
-- canonical owner-side condition ensuring the point is finite-valued, and it pulls back to
-- `x ∈ interior (finite_domain (fun y ↦ f (φ y)))`. The directional-derivative formula therefore
-- applies without any false `effective_domain`-only shortcut. Then use compact convexity of both
-- subdifferentials and the equality criterion from support functions to conclude equality of the
-- sets.
omit [FiniteDimensional ℝ E] in
/-- Theorem 3.19: affine transformation rule of subdifferential calculus. If
`f` is convex and `φ x ∈ interior (finite_domain f)`, then the subdifferential of
`h = f ∘ φ` at `x` is exactly the pullback of the subdifferential of `f` at `φ x` along the
linear part of `φ`; the interior finite-domain hypothesis for `h` is the affine-preimage
consequence of the displayed assumption. Specializing to `φ y = A y + b` recovers the textbook
notation `∂ h(x) = Aᵀ (∂ f(A x + b))`. -/
theorem subdifferential_precompose_affineMap_eq
    (f : E → EReal) (φ : V →ᵃ[ℝ] E) (x : V)
    (hconvex : is_convex_function f)
    (hφx : φ x ∈ interior (finite_domain f)) :
    ∂ (fun y ↦ f (φ y))(x) =
      φ.linear.dualMap '' ∂ f(φ x) := by
  -- The weak inclusion is already available; only the reverse inclusion needs work.
  apply Set.Subset.antisymm
  · intro g hg
    letI : IsProperExtendedRealFunction f :=
      properExtendedRealFunctionOfConvexInteriorFiniteDomain
        f (φ x) hconvex hφx
    have hφx_effective : φ x ∈ interior (effective_domain f) := by
      simpa [finite_domain_eq_effective_domain IsProperExtendedRealFunction.ne_bot]
        using hφx
    have hann :
        g ∈ φ.linear.ker.dualAnnihilator :=
      subgradient_precompose_affineMap_mem_dualAnnihilator
        f φ x hconvex hφx hg
    let gQuot : Module.Dual ℝ (V ⧸ φ.linear.ker) :=
      (Submodule.dualQuotEquivDualAnnihilator (φ.linear.ker)).symm ⟨g, hann⟩
    let rangeToQuot : φ.linear.range ≃ₗ[ℝ] V ⧸ φ.linear.ker :=
      φ.linear.quotKerEquivRange.symm
    let gRange : Module.Dual ℝ φ.linear.range :=
      gQuot.comp rangeToQuot.toLinearMap
    let fRange : E →ₗ.[ℝ] ℝ := LinearPMap.mk φ.linear.range gRange
    let N : E → ℝ := fun z ↦ (directional_derivative f (φ x) z).toReal
    obtain ⟨hN_hom, hN_add⟩ :=
      directionalDerivativeToRealSublinear
        hconvex hφx_effective
    have hf_le : ∀ z : fRange.domain, fRange z ≤ N z := by
      intro z
      rcases z with ⟨z, hz⟩
      rcases hz with ⟨v, rfl⟩
      -- Evaluate the factorized functional on a represented range point.
      have hgRange :
          gRange ⟨φ.linear v, LinearMap.mem_range_self φ.linear v⟩ = g v := by
        dsimp [gRange, gQuot]
        rw [LinearMap.quotKerEquivRange_symm_apply_image]
        rw [Submodule.mkQ_apply]
        rw [Submodule.dualQuotEquivDualAnnihilator_symm_apply_mk]
        rfl
      simpa [fRange, N, hgRange] using
        subgradient_precompose_affineMap_le_targetDirectionalDerivative
          f φ x hconvex hφx hg v
    obtain ⟨d, hd_ext, hd_le⟩ :=
      exists_extension_of_le_sublinear fRange N hN_hom hN_add hf_le
    have hd_sub : d ∈ ∂ f(φ x) :=
      dominatedLinearFunctional_memSubdifferential
        hconvex hφx_effective hd_le
    refine ⟨d, hd_sub, ?_⟩
    ext v
    -- The extension agrees with the range factorization on `range φ.linear`.
    have hd_eq :
        d (φ.linear v) =
          gRange ⟨φ.linear v, LinearMap.mem_range_self φ.linear v⟩ :=
      hd_ext ⟨φ.linear v, LinearMap.mem_range_self φ.linear v⟩
    have hgRange :
        gRange ⟨φ.linear v, LinearMap.mem_range_self φ.linear v⟩ = g v := by
      dsimp [gRange, gQuot]
      rw [LinearMap.quotKerEquivRange_symm_apply_image]
      rw [Submodule.mkQ_apply]
      rw [Submodule.dualQuotEquivDualAnnihilator_symm_apply_mk]
      rfl
    simpa [LinearMap.dualMap_apply] using hd_eq.trans hgRange
  · exact subdifferential_precompose_affineMap_subset f φ x

end

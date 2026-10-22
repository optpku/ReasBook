/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_2
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_10
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_8
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_9

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped Pointwise Topology

universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/- Theorem 3.15 is `source-facing` at the chapter owner
`subdifferential : Set (Module.Dual ℝ E)`. The continuous-dual object
`strongDualSubdifferential` from Theorem 3.1 is only a `bridge/view`, so the main declarations
here stay on the owner abstraction instead of restating the theorem after passing to `StrongDual`.
-/
recall subdifferential
recall effective_domain
recall is_convex_function

-- Proof sketch: expand membership in the pointwise sum
-- `subdifferential f₁ x + subdifferential f₂ x`, choose `g₁ ∈ subdifferential f₁ x` and
-- `g₂ ∈ subdifferential f₂ x` with sum `g`,
-- and add the two defining subgradient inequalities to obtain the supporting inequality for
-- `f₁ + f₂` at `x`. Membership in the left-hand side already supplies the effective-domain
-- condition for both summands, so no extra hypotheses are primitive in this weak inclusion.
/-- Weak owner-level inclusion companion for Theorem 3.15.
The textbook proper/convex/effective-domain preamble is redundant for this inclusion, so the
public statement stays at the minimal owner level. -/
theorem sum_subdifferential_subset_subdifferential_add
    (f₁ f₂ : E → EReal) (x : E) :
    ∂ f₁(x) + ∂ f₂(x) ⊆ ∂ (f₁ + f₂)(x) := by
  intro g hg
  rw [Set.mem_add] at hg
  rcases hg with ⟨g₁, hg₁, g₂, hg₂, rfl⟩
  rw [mem_subdifferential] at hg₁ hg₂ ⊢
  refine ⟨mem_effective_domain.mpr ?_, ?_⟩
  · simpa [Pi.add_apply] using
      EReal.add_lt_top (mem_effective_domain.mp hg₁.1).ne (mem_effective_domain.mp hg₂.1).ne
  intro y
  have hy₁ : f₁ x + (g₁ (y - x) : EReal) ≤ f₁ y := by
    simpa [ge_iff_le] using hg₁.2 y
  have hy₂ : f₂ x + (g₂ (y - x) : EReal) ≤ f₂ y := by
    simpa [ge_iff_le] using hg₂.2 y
  -- Add the two defining affine lower bounds pointwise.
  have hsum :
      (f₁ x + (g₁ (y - x) : EReal)) + (f₂ x + (g₂ (y - x) : EReal)) ≤
        f₁ y + f₂ y :=
    add_le_add hy₁ hy₂
  simpa [Pi.add_apply, LinearMap.add_apply, EReal.coe_add, add_assoc, add_left_comm, add_comm,
    ge_iff_le] using hsum

/-- Companion to Theorem 3.15 (1): if `f₁` and `f₂` are convex, never attain `⊥`, and `x` lies
in both effective domains, then the pointwise sum of the two subdifferentials at `x` is
contained in the subdifferential of the pointwise sum. -/
theorem sum_subdifferential_subset_subdifferential_add_of_convex_effectiveDomain
    (f₁ f₂ : E → EReal) (x : E)
    (h_ne_bot₁ : ∀ y, f₁ y ≠ ⊥)
    (h_ne_bot₂ : ∀ y, f₂ y ≠ ⊥)
    (hconvex₁ : is_convex_function f₁)
    (hconvex₂ : is_convex_function f₂)
    (hx₁ : x ∈ effective_domain f₁)
    (hx₂ : x ∈ effective_domain f₂) :
    ∂ f₁(x) + ∂ f₂(x) ⊆ ∂ (f₁ + f₂)(x) := by
  let _ := h_ne_bot₁
  let _ := h_ne_bot₂
  let _ := hconvex₁
  let _ := hconvex₂
  let _ := hx₁
  let _ := hx₂
  simpa using sum_subdifferential_subset_subdifferential_add f₁ f₂ x

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

-- Semantic recall note: no direct mathlib sum-rule analogue surfaced in semantic search, and the
-- local Chapter 3 precedent in `Theorem_3_8` and `Theorem_3_13` keeps the owner API on
-- `interior (finite_domain _)`, deriving `effective_domain` variants via
-- `finite_domain_eq_effective_domain`.
recall finite_domain
recall effective_domain
recall is_convex_function
recall IsProperExtendedRealFunction
recall properExtendedRealFunctionOfConvexInteriorFiniteDomain
recall directionalDerivative_eq_coe_toReal_at_interior_point
recall directionalDerivativeToRealSublinear
recall dominatedLinearFunctional_memSubdifferential
recall subgradient_pairing_le_directional_derivative_at_interior_point
recall exists_real_has_directional_derivative_at_of_convex_interior_point
recall eventuallyMemFiniteDomainAlong
recall tendstoRealDirectionalQuotientOfHasDirectionalDerivativeAt

/- Part (2) keeps the owner theorem on `interior (finite_domain _)`, while the textbook
source-facing formulation with `effective_domain` remains a separate labeled companion. -/

/-- Helper for Theorem 3.15: interior finite-domain points for `f₁` and `f₂` remain interior
finite-domain points for the pointwise sum `f₁ + f₂`. -/
lemma memInterior_finiteDomain_add_of_memInteriors
    {f₁ f₂ : E → EReal} {x : E}
    (hconvex₁ : is_convex_function f₁)
    (hconvex₂ : is_convex_function f₂)
    (hx₁ : x ∈ interior (finite_domain f₁))
    (hx₂ : x ∈ interior (finite_domain f₂)) :
    x ∈ interior (finite_domain (f₁ + f₂)) := by
  letI : IsProperExtendedRealFunction f₁ :=
    properExtendedRealFunctionOfConvexInteriorFiniteDomain f₁ x hconvex₁ hx₁
  letI : IsProperExtendedRealFunction f₂ :=
    properExtendedRealFunctionOfConvexInteriorFiniteDomain f₂ x hconvex₂ hx₂
  let hne₁ : ∀ y, f₁ y ≠ ⊥ := IsProperExtendedRealFunction.ne_bot
  let hne₂ : ∀ y, f₂ y ≠ ⊥ := IsProperExtendedRealFunction.ne_bot
  have hsum_ne_bot : ∀ y, (f₁ + f₂) y ≠ ⊥ := by
    intro y
    simpa [Pi.add_apply] using EReal.add_ne_bot_iff.mpr ⟨hne₁ y, hne₂ y⟩
  have hsubset :
      finite_domain f₁ ∩ finite_domain f₂ ⊆ finite_domain (f₁ + f₂) := by
    intro y hy
    rcases hy with ⟨hy₁, hy₂⟩
    rcases hy₁ with ⟨hy₁_eff, hy₁_ne_bot⟩
    rcases hy₂ with ⟨hy₂_eff, hy₂_ne_bot⟩
    refine ⟨?_, hsum_ne_bot y⟩
    exact mem_effective_domain.mpr <| by
      simpa [Pi.add_apply] using
        EReal.add_lt_top (mem_effective_domain.mp hy₁_eff).ne (mem_effective_domain.mp hy₂_eff).ne
  -- First intersect the two interior neighborhoods, then push them into the sum finite domain.
  have hx_inter : x ∈ interior (finite_domain f₁ ∩ finite_domain f₂) := by
    simpa [interior_inter] using Set.mem_inter hx₁ hx₂
  exact interior_mono hsubset hx_inter

/-- Helper for Theorem 3.15: the real-valued directional derivative of `f₁ + f₂` is bounded above
by the sum of the two real-valued directional derivatives at a common interior finite-domain point.
-/
lemma directionalDerivativeToReal_add_le_of_memInteriors
    {f₁ f₂ : E → EReal} {x d : E}
    (hconvex₁ : is_convex_function f₁)
    (hconvex₂ : is_convex_function f₂)
    (hx₁ : x ∈ interior (finite_domain f₁))
    (hx₂ : x ∈ interior (finite_domain f₂)) :
    (directional_derivative (f₁ + f₂) x d).toReal ≤
      (directional_derivative f₁ x d).toReal + (directional_derivative f₂ x d).toReal := by
  letI : IsProperExtendedRealFunction f₁ :=
    properExtendedRealFunctionOfConvexInteriorFiniteDomain f₁ x hconvex₁ hx₁
  letI : IsProperExtendedRealFunction f₂ :=
    properExtendedRealFunctionOfConvexInteriorFiniteDomain f₂ x hconvex₂ hx₂
  let hne₁ : ∀ y, f₁ y ≠ ⊥ := IsProperExtendedRealFunction.ne_bot
  let hne₂ : ∀ y, f₂ y ≠ ⊥ := IsProperExtendedRealFunction.ne_bot
  have hsumConvex : is_convex_function (f₁ + f₂) := by
    exact is_convex_function_pointwise_add hconvex₁ hconvex₂ hne₁ hne₂
  have hxSum : x ∈ interior (finite_domain (f₁ + f₂)) :=
    memInterior_finiteDomain_add_of_memInteriors hconvex₁ hconvex₂ hx₁ hx₂
  rcases exists_real_has_directional_derivative_at_of_convex_interior_point
      (f₁ + f₂) x d hsumConvex hxSum with
    ⟨ℓsum, hℓsum⟩
  rcases exists_real_has_directional_derivative_at_of_convex_interior_point
      f₁ x d hconvex₁ hx₁ with
    ⟨ℓ₁, hℓ₁⟩
  rcases exists_real_has_directional_derivative_at_of_convex_interior_point
      f₂ x d hconvex₂ hx₂ with
    ⟨ℓ₂, hℓ₂⟩
  let qsum : ℝ → ℝ := fun α ↦
    (((f₁ + f₂) (x + α • d)).toReal - ((f₁ + f₂) x).toReal) / α
  let q₁ : ℝ → ℝ := fun α ↦
    ((f₁ (x + α • d)).toReal - (f₁ x).toReal) / α
  let q₂ : ℝ → ℝ := fun α ↦
    ((f₂ (x + α • d)).toReal - (f₂ x).toReal) / α
  have hqsum : Tendsto qsum (𝓝[>] (0 : ℝ)) (𝓝 ℓsum) :=
    tendstoRealDirectionalQuotientOfHasDirectionalDerivativeAt (f₁ + f₂) x hxSum hℓsum
  have hq₁ : Tendsto q₁ (𝓝[>] (0 : ℝ)) (𝓝 ℓ₁) :=
    tendstoRealDirectionalQuotientOfHasDirectionalDerivativeAt f₁ x hx₁ hℓ₁
  have hq₂ : Tendsto q₂ (𝓝[>] (0 : ℝ)) (𝓝 ℓ₂) :=
    tendstoRealDirectionalQuotientOfHasDirectionalDerivativeAt f₂ x hx₂ hℓ₂
  have hxfd₁ : x ∈ finite_domain f₁ := interior_subset hx₁
  have hxfd₂ : x ∈ finite_domain f₂ := interior_subset hx₂
  have hpos : ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), 0 < α := by
    simpa [Set.mem_Ioi] using
      (eventually_mem_nhdsWithin :
        ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), α ∈ Set.Ioi (0 : ℝ))
  have hrewrite :
      ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), qsum α = q₁ α + q₂ α := by
    filter_upwards
      [eventuallyMemFiniteDomainAlong f₁ x hx₁ d, eventuallyMemFiniteDomainAlong f₂ x hx₂ d,
        hpos] with α hα₁ hα₂ hα
    have hαne : α ≠ 0 := ne_of_gt hα
    have hx₁_top : f₁ x ≠ ⊤ := (mem_effective_domain.mp hxfd₁.1).ne
    have hx₂_top : f₂ x ≠ ⊤ := (mem_effective_domain.mp hxfd₂.1).ne
    have hα₁_top : f₁ (x + α • d) ≠ ⊤ := (mem_effective_domain.mp hα₁.1).ne
    have hα₂_top : f₂ (x + α • d) ≠ ⊤ := (mem_effective_domain.mp hα₂.1).ne
    have hsum_alpha :
        ((f₁ + f₂) (x + α • d)).toReal =
          (f₁ (x + α • d)).toReal + (f₂ (x + α • d)).toReal := by
      rw [Pi.add_apply, EReal.toReal_add hα₁_top hα₁.2 hα₂_top hα₂.2]
    have hsum_x :
        ((f₁ + f₂) x).toReal = (f₁ x).toReal + (f₂ x).toReal := by
      rw [Pi.add_apply, EReal.toReal_add hx₁_top hxfd₁.2 hx₂_top hxfd₂.2]
    -- After converting the finite sum values to real arithmetic, the quotient splits termwise.
    dsimp [qsum, q₁, q₂]
    rw [EReal.toReal_add hα₁_top hα₁.2 hα₂_top hα₂.2,
      EReal.toReal_add hx₁_top hxfd₁.2 hx₂_top hxfd₂.2]
    field_simp [hαne]
    ring
  have hqadd_to_sum : Tendsto (fun α : ℝ ↦ q₁ α + q₂ α) (𝓝[>] (0 : ℝ)) (𝓝 (ℓ₁ + ℓ₂)) :=
    hq₁.add hq₂
  have hqadd_to_lsum : Tendsto (fun α : ℝ ↦ q₁ α + q₂ α) (𝓝[>] (0 : ℝ)) (𝓝 ℓsum) := by
    exact hqsum.congr' hrewrite
  have hlim : ℓsum = ℓ₁ + ℓ₂ := tendsto_nhds_unique hqadd_to_lsum hqadd_to_sum
  -- Rewrite each directional derivative through its finite real witness and conclude.
  rw [directional_derivative_eq_of_has_directional_derivative_at hℓsum,
    directional_derivative_eq_of_has_directional_derivative_at hℓ₁,
    directional_derivative_eq_of_has_directional_derivative_at hℓ₂]
  simpa using le_of_eq hlim

/-- Helper for Theorem 3.15: a linear functional dominated by the sum of two sublinear maps splits
into summands dominated by each sublinear component. -/
lemma exists_linearSplit_le_sublinearSum
    {p₁ p₂ : E → ℝ} {g : Module.Dual ℝ E}
    (hp₁_hom : ∀ a : ℝ, 0 < a → ∀ v : E, p₁ (a • v) = a * p₁ v)
    (hp₁_add : ∀ u v : E, p₁ (u + v) ≤ p₁ u + p₁ v)
    (hp₂_hom : ∀ a : ℝ, 0 < a → ∀ v : E, p₂ (a • v) = a * p₂ v)
    (hp₂_add : ∀ u v : E, p₂ (u + v) ≤ p₂ u + p₂ v)
    (hg : ∀ d : E, g d ≤ p₁ d + p₂ d) :
    ∃ g₁ g₂ : Module.Dual ℝ E,
      g = g₁ + g₂ ∧
        (∀ d : E, g₁ d ≤ p₁ d) ∧
        ∀ d : E, g₂ d ≤ p₂ d := by
  let diag : Submodule ℝ (E × E) := {
    carrier := {z : E × E | z.1 = z.2}
    zero_mem' := by simp
    add_mem' := by
      intro z w hz hw
      change z.1 = z.2 at hz
      change w.1 = w.2 at hw
      simp [hz, hw]
    smul_mem' := by
      intro a z hz
      change z.1 = z.2 at hz
      simp [hz] }
  let φ : (E × E) →ₗ.[ℝ] ℝ := {
    domain := diag
    toFun := {
      toFun := fun z ↦ g (z : E × E).1
      map_add' := by
        intro z w
        simp
      map_smul' := by
        intro a z
        simp } }
  let N : E × E → ℝ := fun z ↦ p₁ z.1 + p₂ z.2
  have hN_hom : ∀ a : ℝ, 0 < a → ∀ z : E × E, N (a • z) = a * N z := by
    intro a ha z
    -- The product majorant is positively homogeneous because each coordinate majorant is.
    calc
      N (a • z) = p₁ (a • z.1) + p₂ (a • z.2) := by rfl
      _ = a * p₁ z.1 + a * p₂ z.2 := by rw [hp₁_hom a ha, hp₂_hom a ha]
      _ = a * N z := by ring
  have hN_add : ∀ z w : E × E, N (z + w) ≤ N z + N w := by
    intro z w
    -- Subadditivity on each coordinate gives subadditivity on the product.
    calc
      N (z + w) = p₁ (z.1 + w.1) + p₂ (z.2 + w.2) := by rfl
      _ ≤ (p₁ z.1 + p₁ w.1) + (p₂ z.2 + p₂ w.2) := by
        exact add_le_add (hp₁_add z.1 w.1) (hp₂_add z.2 w.2)
      _ = N z + N w := by ring
  have hφ_le : ∀ z : φ.domain, φ z ≤ N z := by
    intro z
    -- On the diagonal subspace, the domination hypothesis reads exactly `g d ≤ p₁ d + p₂ d`.
    have hz : (z : E × E).1 = (z : E × E).2 := z.2
    simpa [φ, N, hz] using hg (z : E × E).1
  obtain ⟨G, hG_ext, hG_le⟩ := exists_extension_of_le_sublinear φ N hN_hom hN_add hφ_le
  let g₁ : Module.Dual ℝ E := G.comp (LinearMap.inl ℝ E E)
  let g₂ : Module.Dual ℝ E := G.comp (LinearMap.inr ℝ E E)
  have hp₁_zero : p₁ (0 : E) = 0 := by
    have hzero : p₁ (0 : E) = 2 * p₁ (0 : E) := by
      simpa using hp₁_hom 2 (by norm_num) (0 : E)
    linarith
  have hp₂_zero : p₂ (0 : E) = 0 := by
    have hzero : p₂ (0 : E) = 2 * p₂ (0 : E) := by
      simpa using hp₂_hom 2 (by norm_num) (0 : E)
    linarith
  have hg_diag : ∀ d : E, G (d, d) = g d := by
    intro d
    let z : diag := ⟨(d, d), rfl⟩
    simpa [φ, z] using hG_ext z
  have hg_eq : g = g₁ + g₂ := by
    ext d
    -- The extension equals `g` on the diagonal and splits across the two coordinate axes.
    have hpair : ((d, d) : E × E) = ((d, (0 : E)) : E × E) + (0, d) := by
      ext <;> simp
    calc
      g d = G (d, d) := by symm; exact hg_diag d
      _ = G (((d, (0 : E)) : E × E) + (0, d)) := by rw [hpair]
      _ = G (d, (0 : E)) + G (0, d) := by rw [map_add]
      _ = g₁ d + g₂ d := by rfl
  have hg₁_le : ∀ d : E, g₁ d ≤ p₁ d := by
    intro d
    -- Evaluate the global domination on the first coordinate axis.
    simpa [g₁, N, hp₂_zero] using hG_le (d, (0 : E))
  have hg₂_le : ∀ d : E, g₂ d ≤ p₂ d := by
    intro d
    -- Evaluate the global domination on the second coordinate axis.
    simpa [g₂, N, hp₁_zero] using hG_le ((0 : E), d)
  exact ⟨g₁, g₂, hg_eq, hg₁_le, hg₂_le⟩

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Helper for Theorem 3.15: any subgradient of `f₁ + f₂` at a common interior finite-domain
point splits as a sum of subgradients of `f₁` and `f₂` at the same point. -/
lemma mem_sum_subdifferential_of_mem_subdifferential_add
    {f₁ f₂ : E → EReal} {x : E}
    (hconvex₁ : is_convex_function f₁)
    (hconvex₂ : is_convex_function f₂)
    (hx₁ : x ∈ interior (finite_domain f₁))
    (hx₂ : x ∈ interior (finite_domain f₂))
    {g : Module.Dual ℝ E}
    (hg : g ∈ ∂(f₁ + f₂)(x)) :
    g ∈ ∂ f₁(x) + ∂ f₂(x) := by
  letI : IsProperExtendedRealFunction f₁ :=
    properExtendedRealFunctionOfConvexInteriorFiniteDomain f₁ x hconvex₁ hx₁
  letI : IsProperExtendedRealFunction f₂ :=
    properExtendedRealFunctionOfConvexInteriorFiniteDomain f₂ x hconvex₂ hx₂
  let hne₁ : ∀ y, f₁ y ≠ ⊥ := IsProperExtendedRealFunction.ne_bot
  let hne₂ : ∀ y, f₂ y ≠ ⊥ := IsProperExtendedRealFunction.ne_bot
  have hsumConvex : is_convex_function (f₁ + f₂) := by
    exact is_convex_function_pointwise_add hconvex₁ hconvex₂ hne₁ hne₂
  have hxSum : x ∈ interior (finite_domain (f₁ + f₂)) :=
    memInterior_finiteDomain_add_of_memInteriors hconvex₁ hconvex₂ hx₁ hx₂
  letI : IsProperExtendedRealFunction (f₁ + f₂) :=
    properExtendedRealFunctionOfConvexInteriorFiniteDomain (f₁ + f₂) x hsumConvex hxSum
  let hneSum : ∀ y, (f₁ + f₂) y ≠ ⊥ := IsProperExtendedRealFunction.ne_bot
  have hx₁_eff : x ∈ interior (effective_domain f₁) := by
    simpa [finite_domain_eq_effective_domain hne₁] using hx₁
  have hx₂_eff : x ∈ interior (effective_domain f₂) := by
    simpa [finite_domain_eq_effective_domain hne₂] using hx₂
  have hxSum_eff : x ∈ interior (effective_domain (f₁ + f₂)) := by
    simpa [finite_domain_eq_effective_domain hneSum] using hxSum
  let p₁ : E → ℝ := fun d ↦ (directional_derivative f₁ x d).toReal
  let p₂ : E → ℝ := fun d ↦ (directional_derivative f₂ x d).toReal
  obtain ⟨hp₁_hom, hp₁_add⟩ := directionalDerivativeToRealSublinear hconvex₁ hx₁_eff
  obtain ⟨hp₂_hom, hp₂_add⟩ := directionalDerivativeToRealSublinear hconvex₂ hx₂_eff
  have hg_dom : ∀ d : E, g d ≤ p₁ d + p₂ d := by
    intro d
    -- Compare the subgradient pairing for `f₁ + f₂` against the directional-derivative upper bound.
    have hpair :
        (g d : EReal) ≤ directional_derivative (f₁ + f₂) x d :=
      subgradient_pairing_le_directional_derivative_at_interior_point hsumConvex hxSum_eff hg
    have hsum_coe :
        directional_derivative (f₁ + f₂) x d =
          (((directional_derivative (f₁ + f₂) x d).toReal : ℝ) : EReal) := by
      exact directionalDerivative_eq_coe_toReal_at_interior_point hsumConvex hxSum_eff
    have hdd_le :
        (directional_derivative (f₁ + f₂) x d).toReal ≤ p₁ d + p₂ d :=
      directionalDerivativeToReal_add_le_of_memInteriors hconvex₁ hconvex₂ hx₁ hx₂
    have hbound :
        (g d : EReal) ≤ (((p₁ d + p₂ d : ℝ) : ℝ) : EReal) := by
      rw [hsum_coe] at hpair
      exact hpair.trans (EReal.coe_le_coe hdd_le)
    exact EReal.coe_le_coe_iff.mp hbound
  obtain ⟨g₁, g₂, hg_eq, hg₁_le, hg₂_le⟩ :=
    exists_linearSplit_le_sublinearSum hp₁_hom hp₁_add hp₂_hom hp₂_add hg_dom
  have hg₁_sub : g₁ ∈ ∂ f₁(x) :=
    dominatedLinearFunctional_memSubdifferential hconvex₁ hx₁_eff hg₁_le
  have hg₂_sub : g₂ ∈ ∂ f₂(x) :=
    dominatedLinearFunctional_memSubdifferential hconvex₂ hx₂_eff hg₂_le
  rw [Set.mem_add]
  exact ⟨g₁, hg₁_sub, g₂, hg₂_sub, hg_eq.symm⟩

-- Proof sketch: the inclusion `⊇` is the weak sum rule from part (1). For the converse inclusion,
-- apply the max formula to the proper convex function `f₁ + f₂` at an interior point of its
-- finite domain, use additivity of directional derivatives together with the max formula for each
-- summand, and identify compact convex sets with equal support functions.
/-- Theorem 3.15: owner-level exact two-term sum rule at interior finite-domain points. -/
theorem subdifferential_add_eq_sum_subdifferential_of_mem_interiors
    (f₁ f₂ : E → EReal) (x : E)
    (hconvex₁ : is_convex_function f₁)
    (hconvex₂ : is_convex_function f₂)
    (hx₁ : x ∈ interior (finite_domain f₁))
    (hx₂ : x ∈ interior (finite_domain f₂)) :
    ∂ (f₁ + f₂)(x) = ∂ f₁(x) + ∂ f₂(x) := by
  apply Set.Subset.antisymm
  · -- The reverse inclusion is the Hahn-Banach splitting step packaged below.
    intro g hg
    exact mem_sum_subdifferential_of_mem_subdifferential_add hconvex₁ hconvex₂ hx₁ hx₂ hg
  · -- The easy inclusion is the weak sum rule from part (1).
    exact sum_subdifferential_subset_subdifferential_add f₁ f₂ x

/-- Companion to Theorem 3.15: if `f₁` and `f₂` are proper convex extended-real-valued functions
and `x`
lies in the interior of the effective domains of `f₁` and `f₂`, then the subdifferential of the
pointwise sum is exactly the pointwise sum of the two subdifferentials. -/
theorem subdifferential_add_eq_sum_subdifferential_of_proper_convex
    (f₁ f₂ : E → EReal) [IsProperExtendedRealFunction f₁] [IsProperExtendedRealFunction f₂] (x : E)
    (hconvex₁ : is_convex_function f₁)
    (hconvex₂ : is_convex_function f₂)
    (hx₁ : x ∈ interior (effective_domain f₁))
    (hx₂ : x ∈ interior (effective_domain f₂)) :
    ∂ (f₁ + f₂)(x) = ∂ f₁(x) + ∂ f₂(x) := by
  let h_ne_bot₁ : ∀ y, f₁ y ≠ ⊥ := IsProperExtendedRealFunction.ne_bot
  let h_ne_bot₂ : ∀ y, f₂ y ≠ ⊥ := IsProperExtendedRealFunction.ne_bot
  simpa [finite_domain_eq_effective_domain h_ne_bot₁,
    finite_domain_eq_effective_domain h_ne_bot₂] using
    subdifferential_add_eq_sum_subdifferential_of_mem_interiors f₁ f₂ x hconvex₁ hconvex₂
      (by
        simpa [finite_domain_eq_effective_domain h_ne_bot₁]
          using hx₁)
      (by
        simpa [finite_domain_eq_effective_domain h_ne_bot₂]
          using hx₂)

end

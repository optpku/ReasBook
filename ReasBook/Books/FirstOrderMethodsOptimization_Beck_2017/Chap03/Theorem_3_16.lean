/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_15
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_10

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped BigOperators Pointwise
open scoped Topology

universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]
variable {ι : Type u} [Fintype ι]

/- Theorem 3.16 extends the Chapter 3 subdifferential calculus from Theorem 3.15 to finite
families. The canonical owner-level weak and exact sum rules are the primary public statements, and
the textbook proper/effective-domain formulations are kept only as source-facing companions obtained
from the owner API. -/
recall subdifferential
recall effective_domain
recall IsProperExtendedRealFunction
recall is_convex_function
recall sum_subdifferential_subset_subdifferential_add

/-- Helper for Theorem 3.16: the subdifferential of the zero function is the singleton `{0}`. -/
private lemma subdifferential_zero_eq_singleton
    (x : E) :
    ∂ (fun _ : E ↦ (0 : EReal))(x) = ({0} : Set (Module.Dual ℝ E)) := by
  ext g
  constructor
  · intro hg
    rw [mem_subdifferential] at hg
    have hnonpos : ∀ z : E, g z ≤ 0 := by
      intro z
      have hz := hg.2 (x + z)
      have hshift : x + z - x = z := by
        abel
      have hz' : ((g z : ℝ) : EReal) ≤ (0 : EReal) := by
        simpa [hshift, ge_iff_le] using hz
      exact EReal.coe_le_coe_iff.mp hz'
    have hnonneg : ∀ z : E, 0 ≤ g z := by
      intro z
      have hzneg : -g z ≤ 0 := by
        simpa using hnonpos (-z)
      exact neg_nonpos.mp hzneg
    -- A linear functional bounded above and below by zero must itself be zero.
    have hgzero : g = 0 := by
      ext z
      exact le_antisymm (hnonpos z) (hnonneg z)
    simp [hgzero]
  · intro hg
    have hgzero : g = 0 := by
      simpa using hg
    subst g
    rw [mem_subdifferential]
    constructor
    · simp [effective_domain]
    · intro y
      simp [ge_iff_le]

omit [Fintype ι] in
/-- Helper for Theorem 3.16: any finite pointwise sum of subdifferentials is contained in the
subdifferential of the corresponding finite pointwise sum of functions. -/
private theorem sum_subdifferential_subset_subdifferential_finset_sumOn
    (f : ι → E → EReal) (x : E) (s : Finset ι) :
    s.sum (fun i ↦ ∂ (f i)(x)) ⊆ ∂ (fun y ↦ s.sum (fun i ↦ f i y))(x) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · intro g hg
    simpa [subdifferential_zero_eq_singleton (E := E) (x := x)] using hg
  · intro i s hi ih g hg
    rw [Finset.sum_insert hi, Set.mem_add] at hg
    rcases hg with ⟨g₁, hg₁, g₂, hg₂, rfl⟩
    have hg₂' : g₂ ∈ ∂ (fun y ↦ s.sum (fun j ↦ f j y))(x) := ih hg₂
    have hsum :
        g₁ + g₂ ∈ ∂ (f i + fun y ↦ s.sum (fun j ↦ f j y))(x) := by
      have hmem : g₁ + g₂ ∈ ∂ (f i)(x) + ∂ (fun y ↦ s.sum (fun j ↦ f j y))(x) := by
        rw [Set.mem_add]
        exact ⟨g₁, hg₁, g₂, hg₂', rfl⟩
      exact
        sum_subdifferential_subset_subdifferential_add
          (f i) (fun y ↦ s.sum (fun j ↦ f j y)) x hmem
    -- Rewrite the insert-step sum into a binary pointwise sum before applying the two-term rule.
    simpa [Finset.sum_insert, hi, Pi.add_apply] using hsum

-- Proof sketch: transport the finite index type `ι` across an equivalence
-- `ι ≃ Fin (Fintype.card ι)` and induct on `Fintype.card ι`. The base case is the empty sum, and
-- the inductive step splits off one summand and applies the two-function weak sum rule from
-- Theorem 3.15 to that summand and the remaining finite sum.
/-- Weak rule in Theorem 3.16 (1): the owner-level finite-sum subdifferential inclusion. -/
theorem sum_subdifferential_subset_subdifferential_finset_sum
    (f : ι → E → EReal) (x : E) :
    (∑ i, ∂ f i(x)) ⊆ ∂ (fun y ↦ ∑ i, f i y)(x) := by
  classical
  -- Specialize the finite-sum helper to the universal finite set of indices.
  simpa using
    sum_subdifferential_subset_subdifferential_finset_sumOn
      (f := f) (x := x) (s := Finset.univ)

/- The textbook proper/convex/effective-domain preamble is redundant for part (1), so it remains a
source-facing companion rather than the main owner-level statement. -/
/-- Companion to Theorem 3.16 (1): if `f₁, …, f_m` are proper convex extended-real-valued
functions and
`x ∈ ⋂ i, effective_domain (f i)`, then the pointwise sum of the subdifferentials at `x` is
contained in the subdifferential of the pointwise sum at `x`. -/
theorem sum_subdifferential_subset_subdifferential_finset_sum_of_proper_convex
    (f : ι → E → EReal) (x : E)
    (hproper : ∀ i, IsProperExtendedRealFunction (f i))
    (hconvex : ∀ i, is_convex_function (f i))
    (hx : x ∈ ⋂ i, effective_domain (f i)) :
    (∑ i, ∂ f i(x)) ⊆ ∂ (fun y ↦ ∑ i, f i y)(x) := by
  -- The owner-level weak rule already contains the full conclusion.
  let _ := hproper
  let _ := hconvex
  let _ := hx
  simpa using sum_subdifferential_subset_subdifferential_finset_sum (f := f) (x := x)

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type u} [Fintype ι]

recall finite_domain
recall effective_domain
recall IsProperExtendedRealFunction
recall finite_domain_eq_effective_domain
recall subdifferential_add_eq_sum_subdifferential_of_mem_interiors
recall properExtendedRealFunctionOfConvexInteriorFiniteDomain
recall exists_real_has_directional_derivative_at_of_convex_interior_point
recall eventuallyMemFiniteDomainAlong
recall tendstoRealDirectionalQuotientOfHasDirectionalDerivativeAt
recall directionalDerivativeIsProperExtendedRealFunction
recall directional_derivative_is_convex_function
recall memInterior_finiteDomain_add_of_memInteriors
recall directionalDerivativeToReal_add_le_of_memInteriors
recall exists_linearSplit_le_sublinearSum
recall value_ge_value_add_directional_derivative_of_mem_effective_domain

-- Local precedent follows `Theorem_3_15`: the canonical owner statement lives on
-- `interior (finite_domain _)`, while the source-facing `effective_domain` restatement is a
-- companion derived from `finite_domain_eq_effective_domain`.

omit [Fintype ι] in
/-- Helper for Theorem 3.16: a finite pointwise sum of convex summands remains convex once every
summand is finite on a common interior point. -/
private theorem is_convex_function_finset_sumOn
    (f : ι → E → EReal) (x : E) (s : Finset ι)
    (hconvex : ∀ i ∈ s, is_convex_function (f i))
    (hx : ∀ i ∈ s, x ∈ interior (finite_domain (f i))) :
    is_convex_function (fun y ↦ s.sum (fun i ↦ f i y)) := by
  have hne_bot : ∀ i ∈ s, ∀ y, f i y ≠ ⊥ := by
    intro i hi y
    letI : IsProperExtendedRealFunction (f i) :=
      properExtendedRealFunctionOfConvexInteriorFiniteDomain
        (f := f i) (x := x) (hconvex i hi) (hx i hi)
    exact IsProperExtendedRealFunction.ne_bot (f := f i) y
  -- Reuse the Chapter 2 weighted-sum convexity theorem with unit weights.
  simpa using
    is_convex_function_finset_nonneg_weighted_sum s hconvex hne_bot (fun _ ↦ 1)

omit [Fintype ι] in
/-- Helper for Theorem 3.16: a common interior finite-domain point for the summands remains an
interior finite-domain point for any finite pointwise sum. -/
private theorem memInterior_finiteDomain_finset_sumOn
    (f : ι → E → EReal) (x : E) (s : Finset ι)
    (hconvex : ∀ i ∈ s, is_convex_function (f i))
    (hx : ∀ i ∈ s, x ∈ interior (finite_domain (f i))) :
    x ∈ interior (finite_domain (fun y ↦ s.sum (fun i ↦ f i y))) := by
  classical
  revert hconvex hx
  refine Finset.induction_on s ?_ ?_
  · intro hconvex hx
    simp [finite_domain, effective_domain]
  · intro i s hi ih hconvex hx
    have hconvex_i : is_convex_function (f i) := hconvex i (Finset.mem_insert_self i s)
    have hx_i : x ∈ interior (finite_domain (f i)) := hx i (Finset.mem_insert_self i s)
    have hconvex_s : ∀ j ∈ s, is_convex_function (f j) := by
      intro j hj
      exact hconvex j (Finset.mem_insert_of_mem hj)
    have hx_s : ∀ j ∈ s, x ∈ interior (finite_domain (f j)) := by
      intro j hj
      exact hx j (Finset.mem_insert_of_mem hj)
    have htailConvex :
        is_convex_function (fun y ↦ s.sum (fun j ↦ f j y)) :=
      is_convex_function_finset_sumOn f x s hconvex_s hx_s
    have htailInterior :
        x ∈ interior (finite_domain (fun y ↦ s.sum (fun j ↦ f j y))) :=
      ih hconvex_s hx_s
    -- Reduce the insert case to the established two-function interior lemma.
    simpa [Finset.sum_insert, hi, Pi.add_apply] using
      memInterior_finiteDomain_add_of_memInteriors hconvex_i htailConvex hx_i htailInterior

/-- Helper for Theorem 3.16: at an interior finite-domain point of a convex function, every
directional derivative is finite and equals its `toReal` coercion. -/
private lemma directionalDerivative_eq_coe_toReal_of_memInterior_finiteDomain
    {f : E → EReal} {x v : E}
    (hconvex : is_convex_function f) (hx : x ∈ interior (finite_domain f)) :
    directional_derivative f x v = ((directional_derivative f x v).toReal : EReal) := by
  rcases exists_real_has_directional_derivative_at_of_convex_interior_point
      (f := f) (x := x) (d := v) hconvex hx with
    ⟨ℓ, hℓ⟩
  -- The directional derivative is represented by the finite real witness from Theorem 3.8.
  rw [directional_derivative_eq_of_has_directional_derivative_at hℓ]
  simp

/-- Helper for Theorem 3.16: the real-valued directional derivative is subadditive in the
direction variable at an interior finite-domain point. -/
private lemma directionalDerivativeToReal_add_le_at_interior_finiteDomain
    {f : E → EReal} {x u v : E}
    (hconvex : is_convex_function f) (hx : x ∈ interior (finite_domain f)) :
    (directional_derivative f x (u + v)).toReal ≤
      (directional_derivative f x u).toReal + (directional_derivative f x v).toReal := by
  letI : IsProperExtendedRealFunction f :=
    properExtendedRealFunctionOfConvexInteriorFiniteDomain
      (f := f) (x := x) hconvex hx
  letI : IsProperExtendedRealFunction (directional_derivative f x) :=
    directionalDerivativeIsProperExtendedRealFunction (f := f) (x := x) hconvex hx
  have hconv_toReal :
      ConvexOn ℝ (effective_domain (directional_derivative f x))
        (fun w : E ↦ (directional_derivative f x w).toReal) :=
    convexOn_toReal_of_is_convex_function_of_proper
      (directional_derivative f x)
      (directional_derivative_is_convex_function (f := f) (x := x) hconvex hx)
  have hu_dom : u ∈ effective_domain (directional_derivative f x) := by
    refine mem_effective_domain.mpr ?_
    rw [directionalDerivative_eq_coe_toReal_of_memInterior_finiteDomain
      (f := f) (x := x) (v := u) hconvex hx]
    exact EReal.coe_lt_top _
  have hv_dom : v ∈ effective_domain (directional_derivative f x) := by
    refine mem_effective_domain.mpr ?_
    rw [directionalDerivative_eq_coe_toReal_of_memInterior_finiteDomain
      (f := f) (x := x) (v := v) hconvex hx]
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
    -- Positive homogeneity reduces the full sum to the midpoint combination.
    simpa [smul_add, smul_smul, EReal.toReal_mul, add_comm, add_left_comm, add_assoc] using
      congrArg EReal.toReal
        (directional_derivative_nonneg_smul
          (f := f) (x := x) hconvex hx 2 (by norm_num)
          ((1 / 2 : ℝ) • u + (1 / 2 : ℝ) • v))
  linarith

/-- Helper for Theorem 3.16: at an interior finite-domain point, the real-valued directional
derivative satisfies the sublinear hypotheses needed for the Hahn-Banach splitting step. -/
private lemma directionalDerivativeToRealSublinear_of_memInterior_finiteDomain
    {f : E → EReal} {x : E}
    (hconvex : is_convex_function f) (hx : x ∈ interior (finite_domain f)) :
    (∀ a : ℝ, 0 < a → ∀ v : E,
        (directional_derivative f x (a • v)).toReal =
          a * (directional_derivative f x v).toReal) ∧
      ∀ u v : E,
        (directional_derivative f x (u + v)).toReal ≤
          (directional_derivative f x u).toReal + (directional_derivative f x v).toReal := by
  refine ⟨?_, ?_⟩
  · intro a ha v
    -- Positive homogeneity is inherited directly from the owner directional derivative.
    simpa [EReal.toReal_mul] using
      congrArg EReal.toReal
        (directional_derivative_nonneg_smul (f := f) (x := x) hconvex hx a ha.le v)
  · intro u v
    exact directionalDerivativeToReal_add_le_at_interior_finiteDomain
      (f := f) (x := x) (u := u) (v := v) hconvex hx

/-- Helper for Theorem 3.16: a linear functional dominated by the real-valued directional
derivative belongs to the subdifferential at an interior finite-domain point. -/
private lemma dominatedLinearFunctional_memSubdifferential_of_memInterior_finiteDomain
    {f : E → EReal} {x : E}
    (hconvex : is_convex_function f) (hx : x ∈ interior (finite_domain f))
    {g : Module.Dual ℝ E}
    (hg_dom : ∀ v : E, g v ≤ (directional_derivative f x v).toReal) :
    g ∈ ∂ f(x) := by
  letI : IsProperExtendedRealFunction f :=
    properExtendedRealFunctionOfConvexInteriorFiniteDomain
      (f := f) (x := x) hconvex hx
  let h_ne_bot : ∀ y, f y ≠ ⊥ := IsProperExtendedRealFunction.ne_bot (f := f)
  have hxEff : x ∈ interior (effective_domain f) := by
    simpa [finite_domain_eq_effective_domain h_ne_bot] using hx
  rw [mem_subdifferential, is_subgradient_at_iff_forall_mem_effective_domain]
  refine ⟨(interior_subset hx).1, ?_⟩
  intro y hy
  have hpair :
      (g (y - x) : EReal) ≤ directional_derivative f x (y - x) := by
    rw [directionalDerivative_eq_coe_toReal_of_memInterior_finiteDomain
      (f := f) (x := x) (v := y - x) hconvex hx]
    exact EReal.coe_le_coe (hg_dom (y - x))
  have hsupport :
      f y ≥ f x + directional_derivative f x (y - x) :=
    value_ge_value_add_directional_derivative_of_mem_effective_domain
      f x y hconvex h_ne_bot hxEff hy
  -- Compare the dominated linear functional against the directional-derivative support bound.
  have hsum :
      f x + (g (y - x) : EReal) ≤ f x + directional_derivative f x (y - x) := by
    simpa [add_comm] using add_le_add_left hpair (f x)
  exact le_trans hsum (by simpa [ge_iff_le] using hsupport)

/-- Helper for Theorem 3.16: every subgradient pairing is bounded above by the directional
derivative at an interior finite-domain point. -/
private lemma subgradientPairing_leDirectionalDerivative_of_memInterior_finiteDomain
    {f : E → EReal} {x d : E}
    (hconvex : is_convex_function f) (hx : x ∈ interior (finite_domain f))
    {g : Module.Dual ℝ E} (hg : g ∈ ∂f(x)) :
    (g d : EReal) ≤ directional_derivative f x d := by
  letI : IsProperExtendedRealFunction f :=
    properExtendedRealFunctionOfConvexInteriorFiniteDomain
      (f := f) (x := x) hconvex hx
  let h_ne_bot : ∀ y, f y ≠ ⊥ := IsProperExtendedRealFunction.ne_bot (f := f)
  rcases exists_real_has_directional_derivative_at_of_convex_interior_point
      (f := f) (x := x) (d := d) hconvex hx with
    ⟨ℓ, hℓ⟩
  have hquot :
      Tendsto (fun α : ℝ ↦ (f (x + α • d) - f x) / (α : EReal))
        (𝓝[>] (0 : ℝ)) (𝓝 ((ℓ : ℝ) : EReal)) := hℓ
  have hdom :
      ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), x + α • d ∈ effective_domain f := by
    filter_upwards [eventuallyMemFiniteDomainAlong (f := f) (x := x) hx d] with α hα
    exact hα.1
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
    have hx_top : f x ≠ ⊤ := (mem_effective_domain.mp (interior_subset hx).1).ne
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

/-- Helper for Theorem 3.16: any subgradient of a two-block pointwise sum at a common interior
finite-domain point splits into subgradients of the two blocks. -/
private lemma mem_sum_subdifferential_of_mem_subdifferential_add_at_commonInterior
    {f₁ f₂ : E → EReal} {x : E}
    (hconvex₁ : is_convex_function f₁)
    (hconvex₂ : is_convex_function f₂)
    (hx₁ : x ∈ interior (finite_domain f₁))
    (hx₂ : x ∈ interior (finite_domain f₂))
    {g : Module.Dual ℝ E}
    (hg : g ∈ ∂(f₁ + f₂)(x)) :
    g ∈ ∂ f₁(x) + ∂ f₂(x) := by
  letI : IsProperExtendedRealFunction f₁ :=
    properExtendedRealFunctionOfConvexInteriorFiniteDomain
      (f := f₁) (x := x) hconvex₁ hx₁
  letI : IsProperExtendedRealFunction f₂ :=
    properExtendedRealFunctionOfConvexInteriorFiniteDomain
      (f := f₂) (x := x) hconvex₂ hx₂
  have hsumConvex : is_convex_function (f₁ + f₂) := by
    exact is_convex_function_pointwise_add hconvex₁ hconvex₂
      (IsProperExtendedRealFunction.ne_bot (f := f₁))
      (IsProperExtendedRealFunction.ne_bot (f := f₂))
  have hxSum : x ∈ interior (finite_domain (f₁ + f₂)) :=
    memInterior_finiteDomain_add_of_memInteriors hconvex₁ hconvex₂ hx₁ hx₂
  let p₁ : E → ℝ := fun d ↦ (directional_derivative f₁ x d).toReal
  let p₂ : E → ℝ := fun d ↦ (directional_derivative f₂ x d).toReal
  obtain ⟨hp₁_hom, hp₁_add⟩ :=
    directionalDerivativeToRealSublinear_of_memInterior_finiteDomain
      (f := f₁) (x := x) hconvex₁ hx₁
  obtain ⟨hp₂_hom, hp₂_add⟩ :=
    directionalDerivativeToRealSublinear_of_memInterior_finiteDomain
      (f := f₂) (x := x) hconvex₂ hx₂
  have hg_dom : ∀ d : E, g d ≤ p₁ d + p₂ d := by
    intro d
    have hpair :
        (g d : EReal) ≤ directional_derivative (f₁ + f₂) x d :=
      subgradientPairing_leDirectionalDerivative_of_memInterior_finiteDomain
        (f := f₁ + f₂) (x := x) (d := d) hsumConvex hxSum hg
    have hsum_coe :
        directional_derivative (f₁ + f₂) x d =
          (((directional_derivative (f₁ + f₂) x d).toReal : ℝ) : EReal) :=
      directionalDerivative_eq_coe_toReal_of_memInterior_finiteDomain
        (f := f₁ + f₂) (x := x) (v := d) hsumConvex hxSum
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
    dominatedLinearFunctional_memSubdifferential_of_memInterior_finiteDomain
      (f := f₁) (x := x) hconvex₁ hx₁ hg₁_le
  have hg₂_sub : g₂ ∈ ∂ f₂(x) :=
    dominatedLinearFunctional_memSubdifferential_of_memInterior_finiteDomain
      (f := f₂) (x := x) hconvex₂ hx₂ hg₂_le
  rw [Set.mem_add]
  exact ⟨g₁, hg₁_sub, g₂, hg₂_sub, hg_eq.symm⟩

/-- Helper for Theorem 3.16: the exact two-function sum rule holds at a common interior
finite-domain point without adding extra finite-dimensional assumptions. -/
private theorem subdifferential_add_eq_sum_subdifferential_at_commonInterior
    (f₁ f₂ : E → EReal) (x : E)
    (hconvex₁ : is_convex_function f₁)
    (hconvex₂ : is_convex_function f₂)
    (hx₁ : x ∈ interior (finite_domain f₁))
    (hx₂ : x ∈ interior (finite_domain f₂)) :
    ∂ (f₁ + f₂)(x) = ∂ f₁(x) + ∂ f₂(x) := by
  apply Set.Subset.antisymm
  · intro g hg
    exact mem_sum_subdifferential_of_mem_subdifferential_add_at_commonInterior
      hconvex₁ hconvex₂ hx₁ hx₂ hg
  · exact sum_subdifferential_subset_subdifferential_add f₁ f₂ x

omit [Fintype ι] in
/-- Helper for Theorem 3.16: the exact finite-sum rule holds for any finite partial sum once the
summands share a common interior finite-domain point. -/
private theorem subdifferential_finset_sum_eq_sum_subdifferential_sumOn
    (f : ι → E → EReal) (x : E) (s : Finset ι)
    (hconvex : ∀ i ∈ s, is_convex_function (f i))
    (hx : ∀ i ∈ s, x ∈ interior (finite_domain (f i))) :
    ∂ (fun y ↦ s.sum (fun i ↦ f i y))(x) = s.sum (fun i ↦ ∂ (f i)(x)) := by
  classical
  revert hconvex hx
  refine Finset.induction_on s ?_ ?_
  · intro hconvex hx
    ext g
    simp [subdifferential_zero_eq_singleton (E := E) (x := x)]
  · intro i s hi ih hconvex hx
    have hconvex_i : is_convex_function (f i) := hconvex i (Finset.mem_insert_self i s)
    have hx_i : x ∈ interior (finite_domain (f i)) := hx i (Finset.mem_insert_self i s)
    have hconvex_s : ∀ j ∈ s, is_convex_function (f j) := by
      intro j hj
      exact hconvex j (Finset.mem_insert_of_mem hj)
    have hx_s : ∀ j ∈ s, x ∈ interior (finite_domain (f j)) := by
      intro j hj
      exact hx j (Finset.mem_insert_of_mem hj)
    have htailEq :
        ∂ (fun y ↦ s.sum (fun j ↦ f j y))(x) = s.sum (fun j ↦ ∂ (f j)(x)) :=
      ih hconvex_s hx_s
    have htailConvex :
        is_convex_function (fun y ↦ s.sum (fun j ↦ f j y)) :=
      is_convex_function_finset_sumOn f x s hconvex_s hx_s
    have htailInterior :
        x ∈ interior (finite_domain (fun y ↦ s.sum (fun j ↦ f j y))) :=
      memInterior_finiteDomain_finset_sumOn f x s hconvex_s hx_s
    -- Rewrite the insert case as a binary sum and invoke the exact two-block rule.
    have hinsertSum :
        (fun y ↦ (insert i s).sum (fun j ↦ f j y)) =
          f i + fun y ↦ s.sum (fun j ↦ f j y) := by
      funext y
      simp [Finset.sum_insert, hi, Pi.add_apply]
    calc
      subdifferential (fun y ↦ (insert i s).sum (fun j ↦ f j y)) x
          = subdifferential (f i + fun y ↦ s.sum (fun j ↦ f j y)) x := by
              rw [hinsertSum]
      _ = subdifferential (f i) x + subdifferential (fun y ↦ s.sum (fun j ↦ f j y)) x := by
            exact subdifferential_add_eq_sum_subdifferential_at_commonInterior
              (f i) (fun y ↦ s.sum (fun j ↦ f j y)) x hconvex_i htailConvex hx_i htailInterior
      _ = subdifferential (f i) x + s.sum (fun j ↦ subdifferential (f j) x) := by
            rw [htailEq]
      _ = (insert i s).sum (fun j ↦ subdifferential (f j) x) := by
            simp [Finset.sum_insert, hi]

/-- Theorem 3.16 (2): at a common interior finite-domain point, the subdifferential of a finite
pointwise sum is exactly the pointwise sum of the individual subdifferentials. -/
theorem subdifferential_finset_sum_eq_sum_subdifferential_of_mem_iInter_interior_finiteDomain
    (f : ι → E → EReal) (x : E)
    (hconvex : ∀ i, is_convex_function (f i))
    (hx : x ∈ ⋂ i, interior (finite_domain (f i))) :
    ∂ (fun y ↦ ∑ i, f i y)(x) = ∑ i, ∂ f i(x) := by
  classical
  have hconvex_univ : ∀ i ∈ Finset.univ, is_convex_function (f i) := by
    intro i hi
    exact hconvex i
  have hx_univ : ∀ i ∈ Finset.univ, x ∈ interior (finite_domain (f i)) := by
    intro i hi
    exact (Set.mem_iInter.mp hx) i
  -- Specialize the finite-partial-sum theorem to the universal index set.
  simpa using
    subdifferential_finset_sum_eq_sum_subdifferential_sumOn
      (f := f) (x := x) (s := Finset.univ) hconvex_univ hx_univ

-- Proof sketch: transport along `ι ≃ Fin (Fintype.card ι)` and induct on the cardinality.
-- Split off one index, apply the two-function exact sum rule from Theorem 3.15 to that summand
-- and the remaining finite sum, then transport the induction hypothesis back to `ι`. Properness is
-- used only to rewrite `finite_domain` as `effective_domain`, so the source-facing
-- effective-domain formulation is a companion bridge out of the owner theorem above.
/-- Companion to Theorem 3.16 (2): if each summand is a proper convex extended-real-valued
function and
`x ∈ ⋂ i, interior (effective_domain (f i))`, then the subdifferential of the finite pointwise sum
is exactly the pointwise sum of the individual subdifferentials. -/
theorem subdifferential_finset_sum_eq_sum_subdifferential_of_mem_iInter_interior
    (f : ι → E → EReal) (x : E)
    (hproper : ∀ i, IsProperExtendedRealFunction (f i))
    (hconvex : ∀ i, is_convex_function (f i))
    (hx : x ∈ ⋂ i, interior (effective_domain (f i))) :
    ∂ (fun y ↦ ∑ i, f i y)(x) = ∑ i, ∂ f i(x) := by
  have hx_finite : x ∈ ⋂ i, interior (finite_domain (f i)) := by
    rw [Set.mem_iInter]
    intro i
    have hx_i : x ∈ interior (effective_domain (f i)) := (Set.mem_iInter.mp hx) i
    simpa [finite_domain_eq_effective_domain (hproper i).ne_bot] using hx_i
  -- Rewrite the source-facing interior-effective-domain hypotheses back to the owner theorem.
  simpa using
    subdifferential_finset_sum_eq_sum_subdifferential_of_mem_iInter_interior_finiteDomain
      (f := f) (x := x) hconvex hx_finite

end

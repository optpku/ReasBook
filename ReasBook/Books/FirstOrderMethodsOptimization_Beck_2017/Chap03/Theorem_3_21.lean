/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Lemma_2_4
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_10
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_3
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_4
import Mathlib.Analysis.LocallyConvex.Separation

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise
open Filter
open scoped Topology

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {f : E → ℝ} {g : ℝ → ℝ} {x : E}

/-
Theorem 3.21 is `source-facing` in the Chapter 3 convex-analysis API. Its `core/canonical` owner
is the real-valued strong-dual subdifferential `subdifferentialAt` from Theorem 3.4, so this file
keeps only the composition rule for that owner set-valued map and does not introduce any parallel
wrapper or auxiliary packaged notion.
-/
recall subdifferentialAt

/-- Helper for Theorem 3.21: a real-valued convex function on all of `E` remains convex after
coercion to `EReal`. -/
lemma is_convexFunction_coe_of_convexOn
    {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) :
    is_convex_function (fun y ↦ (f y : EReal)) := by
  -- Rewrite the everywhere-finite `EReal` function through its real-valued `ConvexOn` owner.
  refine (is_convex_function_iff_convexOn_toReal ?_).2 ?_
  · intro y hy
    simp
  · simpa [effective_domain] using hf

/-- Helper for Theorem 3.21: evaluating the continuous representative of an algebraic dual
functional recovers the original pairing. -/
lemma toContinuousLinearMap_apply_eq_eval
    (φ : Module.Dual ℝ E) (d : E) :
    ContinuousLinearMap.apply ℝ ℝ d (LinearMap.toContinuousLinearMap φ) = φ d :=
  rfl

/-- Helper for Theorem 3.21: differentiating `g ∘ f` along the ray `t ↦ x + t • d` scales the
directional derivative of `f` by `deriv g (f x)`. -/
lemma directional_derivative_comp_eq_smul
    (hf : ConvexOn ℝ Set.univ f) (hg_diff : DifferentiableAt ℝ g (f x))
    (d : E) :
    directional_derivative (fun y ↦ ((g (f y)) : EReal)) x d =
      ((deriv g (f x) : ℝ) : EReal) * directional_derivative (fun y ↦ (f y : EReal)) x d := by
  let fEReal : E → EReal := fun y ↦ (f y : EReal)
  let lineF : ℝ → ℝ := fun t ↦ f (x + t • d)
  let lineH : ℝ → ℝ := fun t ↦ g (lineF t)
  have hconvex : is_convex_function fEReal :=
    is_convexFunction_coe_of_convexOn hf
  have hx : x ∈ interior (finite_domain fEReal) := by
    simp [fEReal, finite_domain, effective_domain]
  rcases exists_real_has_directional_derivative_at_of_convex_interior_point
      (f := fEReal) (x := x) (d := d) hconvex hx with ⟨ℓ, hℓ⟩
  have hlineF_tendsto :
      Tendsto (fun t : ℝ ↦ (lineF t - lineF 0) / t) (𝓝[>] (0 : ℝ)) (𝓝 ℓ) := by
    -- The Chapter 3 right-quotient bridge identifies the ray restriction with the directional
    -- derivative witness.
    simpa [lineF, fEReal] using
      tendstoRealDirectionalQuotientOfHasDirectionalDerivativeAt (f := fEReal) (x := x) hx hℓ
  have hlineF :
      HasDerivWithinAt lineF ℓ (Set.Ioi (0 : ℝ)) 0 := by
    -- Repackage the right-hand quotient limit as a `HasDerivWithinAt` statement on `Ioi 0`.
    rw [hasDerivWithinAt_iff_tendsto_slope' (by simp : (0 : ℝ) ∉ Set.Ioi (0 : ℝ))]
    refine hlineF_tendsto.congr' ?_
    filter_upwards with t
    simpa using (slope_def_field lineF 0 t).symm
  have hlineH :
      HasDerivWithinAt lineH (deriv g (f x) * ℓ) (Set.Ioi (0 : ℝ)) 0 := by
    -- Apply the one-dimensional chain rule at the ray restriction.
    have hg_hasDeriv :
        HasDerivAt g (deriv g (f x)) (lineF 0) := by
      simpa [lineF] using hg_diff.hasDerivAt
    simpa [lineH, lineF] using hg_hasDeriv.comp_hasDerivWithinAt (x := 0) hlineF
  have hlineH_tendsto :
      Tendsto (fun t : ℝ ↦ (lineH t - lineH 0) / t) (𝓝[>] (0 : ℝ))
        (𝓝 (deriv g (f x) * ℓ)) := by
    -- Convert the derivative statement back to the right-hand quotient used by
    -- `has_directional_derivative_at`.
    have hlineH_slope :
        Tendsto (slope lineH 0) (𝓝[>] (0 : ℝ)) (𝓝 (deriv g (f x) * ℓ)) :=
      (hasDerivWithinAt_iff_tendsto_slope' (f := lineH) (s := Set.Ioi (0 : ℝ)) (x := 0)
        (by simp)).1 hlineH
    refine hlineH_slope.congr' ?_
    filter_upwards with t
    simpa using slope_def_field lineH 0 t
  have hcomp :
      has_directional_derivative_at (fun y ↦ ((g (f y)) : EReal)) x d
        (((deriv g (f x) * ℓ : ℝ)) : EReal) := by
    -- The real right quotient is the `EReal` directional quotient because both endpoint values are
    -- finite along the whole ray.
    refine (EReal.tendsto_coe.2 hlineH_tendsto).congr' ?_
    filter_upwards with t
    simp [lineH, lineF, EReal.coe_sub, EReal.coe_div]
  -- Close by identifying both directional derivatives with their finite real representatives.
  calc
    directional_derivative (fun y ↦ ((g (f y)) : EReal)) x d =
        (((deriv g (f x) * ℓ : ℝ)) : EReal) := by
      exact directional_derivative_eq_of_has_directional_derivative_at hcomp
    _ = ((deriv g (f x) : ℝ) : EReal) * directional_derivative (fun y ↦ (f y : EReal)) x d := by
      rw [directional_derivative_eq_of_has_directional_derivative_at hℓ, EReal.coe_mul]

/-- Helper for Theorem 3.21: for a real-valued convex function, the support function of
`subdifferentialAt f x` evaluated at a point-evaluation functional agrees with the Chapter 3
directional derivative. -/
lemma support_function_subdifferentialAt_eq_directional_derivative
    (hf : ConvexOn ℝ Set.univ f) (x : E) (d : E) :
    support_function (subdifferentialAt f x) (ContinuousLinearMap.apply ℝ ℝ d) =
      directional_derivative (fun y ↦ (f y : EReal)) x d := by
  let fEReal : E → EReal := fun y ↦ (f y : EReal)
  have hconvex : is_convex_function fEReal :=
    is_convexFunction_coe_of_convexOn hf
  have hx : x ∈ interior (finite_domain fEReal) := by
    simp [fEReal, finite_domain, effective_domain]
  -- First rewrite the strong-dual support function back to the owner algebraic-dual set.
  have hbridge :
      support_function (subdifferentialAt f x) (ContinuousLinearMap.apply ℝ ℝ d) =
        support_function (subdifferential fEReal x) (Module.Dual.eval ℝ E d) := by
    rw [subdifferentialAt, strongDualSubdifferential_eq_image_subdifferential]
    rw [support_function_apply, support_function_apply]
    congr 1
    ext z
    constructor
    · rintro ⟨ψ, ⟨φ, hφ, rfl⟩, rfl⟩
      exact ⟨φ, hφ, by simp [Module.Dual.eval_apply]⟩
    · rintro ⟨φ, hφ, rfl⟩
      exact ⟨LinearMap.toContinuousLinearMap φ, ⟨φ, hφ, rfl⟩, by simp [Module.Dual.eval_apply]⟩
  -- Then apply the owner max formula from Proposition 3.10.
  calc
    support_function (subdifferentialAt f x) (ContinuousLinearMap.apply ℝ ℝ d) =
        support_function (subdifferential fEReal x) (Module.Dual.eval ℝ E d) := hbridge
    _ = directional_derivative fEReal x d := by
      symm
      simpa [fEReal] using
        directional_derivative_eq_support_function_subdifferential_at_interior_point
          (f := fEReal) (x := x) (d := d) hconvex hx

/-- Helper for Theorem 3.21: every continuous linear functional on the strong dual of `E` is
evaluation at some point of `E`. -/
lemma continuousLinearFunctionalOnStrongDual_eq_evalAtPoint
    (Λ : StrongDual ℝ (StrongDual ℝ E)) :
    ∃ d : E, Λ = ContinuousLinearMap.apply ℝ ℝ d := by
  let e : (Module.Dual ℝ E) ≃ₗ[ℝ] StrongDual ℝ E := LinearMap.toContinuousLinearMap
  let Λ₀ : Module.Dual ℝ (Module.Dual ℝ E) := Λ.toLinearMap.comp e.toLinearMap
  refine ⟨(Module.evalEquiv ℝ E).symm Λ₀, ?_⟩
  ext ψ
  let φ : Module.Dual ℝ E := e.symm ψ
  have hψ : e φ = ψ := by
    simp [φ]
  -- Normalize `ψ` through the algebraic-dual equivalence and then use reflexivity of `E`.
  calc
    Λ ψ = Λ (e φ) := by rw [hψ]
    _ = Λ₀ φ := rfl
    _ = φ ((Module.evalEquiv ℝ E).symm Λ₀) := by
      simpa [Λ₀] using
        (Module.apply_evalEquiv_symm_apply (R := ℝ) (M := E) φ Λ₀).symm
    _ = (e φ) ((Module.evalEquiv ℝ E).symm Λ₀) := by
      simp [e]
    _ = ψ ((Module.evalEquiv ℝ E).symm Λ₀) := by rw [hψ]
    _ = ContinuousLinearMap.apply ℝ ℝ ((Module.evalEquiv ℝ E).symm Λ₀) ψ := rfl

/-- Helper for Theorem 3.21: the strong-dual subdifferential of a real-valued convex function is
compact in finite dimensions. -/
lemma isCompact_subdifferentialAt_of_convexOn
    {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) (x : E) :
    IsCompact (subdifferentialAt f x) := by
  let fEReal : E → EReal := fun y ↦ (f y : EReal)
  have hconvex : is_convex_function fEReal :=
    is_convexFunction_coe_of_convexOn hf
  have hx : x ∈ interior (effective_domain fEReal) := by
    simp [fEReal, effective_domain]
  have hbounded : Bornology.IsBounded (subdifferentialAt f x) := by
    simpa [subdifferentialAt, fEReal, effective_domain] using
      subdifferential_bounded_at_interior_point
        (f := fEReal) (x := x) (fun y hy ↦ by simp [fEReal])
        hconvex hx
  rcases hbounded.subset_closedBall (0 : StrongDual ℝ E) with ⟨R, hR⟩
  -- Finite-dimensional normed spaces are proper, so closed balls are compact.
  exact (isCompact_closedBall (0 : StrongDual ℝ E) R).of_isClosed_subset
    (isClosed_subdifferential fEReal x) hR

/-- Helper for Theorem 3.21: compact convex subsets of `StrongDual ℝ E` are determined by their
support functions on point-evaluation functionals. -/
lemma eq_of_supportFunction_eq_forall_evalPoint
    {A B : Set (StrongDual ℝ E)} (hA_nonempty : A.Nonempty) (hA_compact : IsCompact A)
    (hA_convex : Convex ℝ A) (hB_nonempty : B.Nonempty) (hB_compact : IsCompact B)
    (hB_convex : Convex ℝ B)
    (hσ : ∀ d : E,
      support_function A (ContinuousLinearMap.apply ℝ ℝ d) =
        support_function B (ContinuousLinearMap.apply ℝ ℝ d)) :
    A = B := by
  have hσ' :
      ∀ l : StrongDual ℝ (StrongDual ℝ E), support_function A l = support_function B l := by
    intro l
    rcases continuousLinearFunctionalOnStrongDual_eq_evalAtPoint l with ⟨d, rfl⟩
    exact hσ d
  apply Set.Subset.antisymm
  · intro z hz
    have hz_halfspaces :
        z ∈ ⋂ l : StrongDual ℝ (StrongDual ℝ E), {w | ∃ y ∈ B, l w ≤ l y} := by
      rw [Set.mem_iInter]
      intro l
      -- Maximize `l` on the compact target set `B` and compare through the support functions.
      obtain ⟨y, hyB, hymax⟩ :=
        hB_compact.exists_isMaxOn hB_nonempty l.continuous.continuousOn
      have hmax_support :
          support_function B l = (l y : EReal) := by
        refine support_function_eq_of_isGreatest_image B l ?_
        refine ⟨⟨y, hyB, rfl⟩, ?_⟩
        rintro _ ⟨w, hw, rfl⟩
        have hwy : l w ≤ l y := hymax hw
        exact (show ((l w : ℝ) : EReal) ≤ ((l y : ℝ) : EReal) from by exact_mod_cast hwy)
      have hzy :
          (l z : EReal) ≤ (l y : EReal) := by
        calc
          (l z : EReal) ≤ support_function A l := le_support_function_of_mem hz l
          _ = support_function B l := hσ' l
          _ = (l y : EReal) := hmax_support
      exact ⟨y, hyB, EReal.coe_le_coe_iff.mp hzy⟩
    simpa [iInter_halfSpaces_eq hB_convex hB_compact.isClosed] using hz_halfspaces
  · intro z hz
    have hz_halfspaces :
        z ∈ ⋂ l : StrongDual ℝ (StrongDual ℝ E), {w | ∃ y ∈ A, l w ≤ l y} := by
      rw [Set.mem_iInter]
      intro l
      -- Repeat the same argument with `A` and `B` swapped.
      obtain ⟨y, hyA, hymax⟩ :=
        hA_compact.exists_isMaxOn hA_nonempty l.continuous.continuousOn
      have hmax_support :
          support_function A l = (l y : EReal) := by
        refine support_function_eq_of_isGreatest_image A l ?_
        refine ⟨⟨y, hyA, rfl⟩, ?_⟩
        rintro _ ⟨w, hw, rfl⟩
        have hwy : l w ≤ l y := hymax hw
        exact (show ((l w : ℝ) : EReal) ≤ ((l y : ℝ) : EReal) from by exact_mod_cast hwy)
      have hzy :
          (l z : EReal) ≤ (l y : EReal) := by
        calc
          (l z : EReal) ≤ support_function B l := le_support_function_of_mem hz l
          _ = support_function A l := (hσ' l).symm
          _ = (l y : EReal) := hmax_support
      exact ⟨y, hyA, EReal.coe_le_coe_iff.mp hzy⟩
    simpa [iInter_halfSpaces_eq hA_convex hA_compact.isClosed] using hz_halfspaces

-- Proof sketch: first note that `g ∘ f` is convex because `f` is convex, `g` is convex, and `g`
-- is monotone. Restrict `f` and `g ∘ f` to any affine line `t ↦ x + t • d`, apply the
-- one-dimensional chain rule to the corresponding directional derivatives at `0`, and obtain
-- `h'(x; d) = g'(f x) * f'(x; d)`. Then identify both directional derivatives with the support
-- functions of the relevant subdifferentials using the Chapter 3 owner bridges for
-- differentiability and positive scalar multiplication, and conclude from equality of support
-- functions of closed convex sets.
/-- Theorem 3.21: chain rule of subdifferential calculus. If `f : E → ℝ` is convex and
`g : ℝ → ℝ` is convex and nondecreasing, and if `g` is differentiable at `f x`, then the
subdifferential of the composition `g ∘ f` at `x` is the scalar multiple of
`subdifferentialAt f x` by the derivative `g'(f x)`. -/
theorem subdifferentialAt_comp_eq_smul_subdifferentialAt
    (hf : ConvexOn ℝ Set.univ f) (hg : ConvexOn ℝ Set.univ g) (hg_mono : Monotone g)
    (hg_diff : DifferentiableAt ℝ g (f x)) :
    subdifferentialAt (g ∘ f) x = (deriv g (f x)) • subdifferentialAt f x := by
  let a : ℝ := deriv g (f x)
  have ha : 0 ≤ a := hg_mono.deriv_nonneg
  have hcomp_convex : ConvexOn ℝ Set.univ (g ∘ f) := by
    -- Convexity of the composition is the source proof's ambient invariant.
    refine ⟨convex_univ, ?_⟩
    intro y hy z hz a' b' ha' hb' hab'
    have hf_le : f (a' • y + b' • z) ≤ a' * f y + b' * f z := by
      simpa [smul_eq_mul] using hf.2 hy hz ha' hb' hab'
    have hg_le : g (a' * f y + b' * f z) ≤ a' * g (f y) + b' * g (f z) := by
      simpa [smul_eq_mul] using hg.2 (by simp) (by simp) ha' hb' hab'
    exact (hg_mono hf_le).trans hg_le
  have hσ :
      ∀ d : E,
        support_function (subdifferentialAt (g ∘ f) x) (ContinuousLinearMap.apply ℝ ℝ d) =
          support_function (a • subdifferentialAt f x) (ContinuousLinearMap.apply ℝ ℝ d) := by
    intro d
    -- Compare the two support functions through directional derivatives and positive homogeneity.
    calc
      support_function (subdifferentialAt (g ∘ f) x) (ContinuousLinearMap.apply ℝ ℝ d) =
          directional_derivative (fun y ↦ ((g (f y)) : EReal)) x d := by
        simpa [Function.comp] using
          support_function_subdifferentialAt_eq_directional_derivative
            (f := g ∘ f) hcomp_convex x d
      _ = ((a : ℝ) : EReal) * directional_derivative (fun y ↦ (f y : EReal)) x d := by
        simpa [a, Function.comp] using directional_derivative_comp_eq_smul hf hg_diff d
      _ = ((a : EReal)) * support_function (subdifferentialAt f x)
            (ContinuousLinearMap.apply ℝ ℝ d) := by
        rw [support_function_subdifferentialAt_eq_directional_derivative (f := f) hf x d]
      _ = support_function (a • subdifferentialAt f x) (ContinuousLinearMap.apply ℝ ℝ d) := by
        symm
        simpa [a, Pi.smul_apply, smul_eq_mul] using
          congrArg
            (fun σ : Module.Dual ℝ (StrongDual ℝ E) → EReal ↦
              σ (ContinuousLinearMap.apply ℝ ℝ d))
            (support_function_smul_set_eq_smul
              (C := subdifferentialAt f x)
              (subdifferentialAt_nonempty_of_convexOn hf x) ha)
  have hA_nonempty : (subdifferentialAt (g ∘ f) x).Nonempty :=
    subdifferentialAt_nonempty_of_convexOn hcomp_convex x
  have hB_nonempty : (a • subdifferentialAt f x).Nonempty := by
    rcases subdifferentialAt_nonempty_of_convexOn hf x with ⟨φ, hφ⟩
    exact ⟨a • φ, Set.smul_mem_smul_set hφ⟩
  have hA_compact : IsCompact (subdifferentialAt (g ∘ f) x) :=
    isCompact_subdifferentialAt_of_convexOn hcomp_convex x
  have hB_compact : IsCompact (a • subdifferentialAt f x) := by
    -- Scalar multiplication sends compact sets to compact sets.
    simpa [Set.image_smul] using
      (isCompact_subdifferentialAt_of_convexOn hf x).image
        (continuous_const.smul continuous_id)
  -- The support functions agree on all evaluation functionals, so compact convexity forces
  -- equality of the two strong-dual subdifferentials.
  exact eq_of_supportFunction_eq_forall_evalPoint
    hA_nonempty hA_compact
    (convex_strongDualSubdifferential (fun y ↦ ((g (f y)) : EReal)) x)
    hB_nonempty hB_compact
    ((convex_strongDualSubdifferential (fun y ↦ (f y : EReal)) x).smul a)
    hσ

/-- Companion specialization of Theorem 3.21 for nonnegative scalar multiplication of a convex
real-valued function. This is the source-facing weighted form used later for distance terms such as
`x ↦ ω * dist x a`. -/
theorem subdifferentialAt_const_mul_eq_smul_subdifferentialAt
    (a : ℝ) (ha : 0 ≤ a) (hf : ConvexOn ℝ Set.univ f) :
    subdifferentialAt (fun y ↦ a * f y) x = a • subdifferentialAt f x := by
  have hderiv : deriv (fun t : ℝ ↦ a * t) (f x) = a := by
    simpa [one_mul] using
      (deriv_const_mul a (differentiableAt_id : DifferentiableAt ℝ (fun t : ℝ ↦ t) (f x)))
  simpa [Function.comp, hderiv] using
    (subdifferentialAt_comp_eq_smul_subdifferentialAt
      hf ((convexOn_id convex_univ).smul ha)
      (monotone_mul_left_of_nonneg ha)
      ((differentiableAt_id : DifferentiableAt ℝ (fun t : ℝ ↦ t) (f x)).const_mul a))

end

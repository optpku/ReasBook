/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Theorem_2_39.Monotonicity
public import Mathlib.Analysis.Calculus.Deriv.AffineMap
public import Mathlib.Analysis.Convex.Deriv

public section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Helper for thm_2_39: subtracting two points on the same segment scales the endpoint
difference by the parameter difference. -/
lemma lineMap_sub_lineMap_eq_smul_sub (x y : H) (s t : ℝ) :
    AffineMap.lineMap x y s - AffineMap.lineMap x y t = (s - t) • (y - x) := by
  -- Rewrite the difference through the common base point `x`.
  have hs : AffineMap.lineMap x y s - x = s • (y - x) := by
    simpa using AffineMap.lineMap_vsub_left x y s
  have ht : AffineMap.lineMap x y t - x = t • (y - x) := by
    simpa using AffineMap.lineMap_vsub_left x y t
  calc
    AffineMap.lineMap x y s - AffineMap.lineMap x y t
        = (AffineMap.lineMap x y s - x) - (AffineMap.lineMap x y t - x) := by
          abel
    _ = s • (y - x) - t • (y - x) := by
          rw [hs, ht]
    _ = (s - t) • (y - x) := by
          rw [sub_smul]

/-- Helper for thm_2_39: the derivative of the restriction of `J` to the segment from `x` to `y`
is the gradient paired with the segment direction `y - x`. -/
lemma deriv_lineRestriction_eq_inner_gradient_sub (J : H → ℝ) (x y : H) (t : ℝ)
    (hJ : DifferentiableAt ℝ J (AffineMap.lineMap x y t)) :
    deriv (fun s : ℝ ↦ J (AffineMap.lineMap x y s)) t =
      inner ℝ (gradient J (AffineMap.lineMap x y t)) (y - x) := by
  -- Differentiate the composition with the affine line map.
  have hcomp :
      HasDerivAt (fun s : ℝ ↦ J (AffineMap.lineMap x y s))
        ((fderiv ℝ J (AffineMap.lineMap x y t)) (y - x)) t := by
    exact hJ.hasFDerivAt.comp_hasDerivAt t AffineMap.hasDerivAt_lineMap
  -- The Fréchet derivative of `J` is the inner product with the gradient.
  calc
    deriv (fun s : ℝ ↦ J (AffineMap.lineMap x y s)) t
        = (fderiv ℝ J (AffineMap.lineMap x y t)) (y - x) := hcomp.deriv
    _ = inner ℝ (gradient J (AffineMap.lineMap x y t)) (y - x) := by
      rw [← inner_gradient_left (f := J) (x := AffineMap.lineMap x y t) (y := y - x)]

/-- Helper for thm_2_39: gradient monotonicity on `C` makes every segment restriction of `J`
have monotone derivative on `Ioo (0 : ℝ) 1`. -/
lemma monotoneOnDeriv_lineRestriction_of_gradientMonotoneOn
    (J : H → ℝ) {C : Set H} (hC : Convex ℝ C) (hJ : ∀ x ∈ C, DifferentiableAt ℝ J x)
    (hmono : GradientMonotoneOn J C) {x y : H} (hx : x ∈ C) (hy : y ∈ C) :
    MonotoneOn (deriv (fun t : ℝ ↦ J (AffineMap.lineMap x y t))) (Set.Ioo (0 : ℝ) 1) := by
  rw [gradientMonotoneOn_iff] at hmono
  intro t₁ ht₁ t₂ ht₂ ht12
  rcases eq_or_lt_of_le ht12 with rfl | ht12
  · exact le_rfl
  · -- Compare the gradients at the two points of the segment and rewrite the result in 1D.
    have hz₁ : AffineMap.lineMap x y t₁ ∈ C := hC.lineMap_mem hx hy ⟨ht₁.1.le, ht₁.2.le⟩
    have hz₂ : AffineMap.lineMap x y t₂ ∈ C := hC.lineMap_mem hx hy ⟨ht₂.1.le, ht₂.2.le⟩
    have hsegment :
        0 ≤ inner ℝ (gradient J (AffineMap.lineMap x y t₂) - gradient J (AffineMap.lineMap x y t₁))
          (AffineMap.lineMap x y t₂ - AffineMap.lineMap x y t₁) := by
      exact hmono hz₂ hz₁
    have hsegment' := hsegment
    rw [lineMap_sub_lineMap_eq_smul_sub, inner_smul_right, inner_sub_left] at hsegment'
    have hdiffInner :
        0 ≤
          inner ℝ (gradient J (AffineMap.lineMap x y t₂)) (y - x) -
            inner ℝ (gradient J (AffineMap.lineMap x y t₁)) (y - x) := by
      exact nonneg_of_mul_nonneg_right hsegment' (sub_pos.mpr ht12)
    have hdiff :
        0 ≤
          deriv (fun t : ℝ ↦ J (AffineMap.lineMap x y t)) t₂ -
            deriv (fun t : ℝ ↦ J (AffineMap.lineMap x y t)) t₁ := by
      simpa [deriv_lineRestriction_eq_inner_gradient_sub J x y t₂ (hJ _ hz₂),
        deriv_lineRestriction_eq_inner_gradient_sub J x y t₁ (hJ _ hz₁)] using hdiffInner
    exact sub_nonneg.mp hdiff

/-- Helper for thm_2_39: strict gradient monotonicity on `C` makes every nontrivial segment
restriction of `J` have strictly monotone derivative on `Ioo (0 : ℝ) 1`. -/
lemma strictMonoOnDeriv_lineRestriction_of_gradientStrictMonotoneOn
    (J : H → ℝ) {C : Set H} (hC : Convex ℝ C) (hJ : ∀ x ∈ C, DifferentiableAt ℝ J x)
    (hmono : GradientStrictMonotoneOn J C) {x y : H} (hx : x ∈ C) (hy : y ∈ C) (hxy : x ≠ y) :
    StrictMonoOn (deriv (fun t : ℝ ↦ J (AffineMap.lineMap x y t))) (Set.Ioo (0 : ℝ) 1) := by
  rw [gradientStrictMonotoneOn_iff] at hmono
  intro t₁ ht₁ t₂ ht₂ ht12
  -- Compare the strict gradient monotonicity inequality with the positive segment factor.
  have hz₁ : AffineMap.lineMap x y t₁ ∈ C := hC.lineMap_mem hx hy ⟨ht₁.1.le, ht₁.2.le⟩
  have hz₂ : AffineMap.lineMap x y t₂ ∈ C := hC.lineMap_mem hx hy ⟨ht₂.1.le, ht₂.2.le⟩
  have hlineNe : AffineMap.lineMap x y t₁ ≠ AffineMap.lineMap x y t₂ := by
    intro hEq
    exact ht12.ne <| (AffineMap.lineMap_injective (k := ℝ) hxy) hEq
  have hsegment :
      0 < inner ℝ (gradient J (AffineMap.lineMap x y t₂) - gradient J (AffineMap.lineMap x y t₁))
        (AffineMap.lineMap x y t₂ - AffineMap.lineMap x y t₁) := by
    exact hmono hz₂ hz₁ hlineNe.symm
  have hsegment' := hsegment
  rw [lineMap_sub_lineMap_eq_smul_sub, inner_smul_right, inner_sub_left] at hsegment'
  have hdiffInner :
      0 <
        inner ℝ (gradient J (AffineMap.lineMap x y t₂)) (y - x) -
          inner ℝ (gradient J (AffineMap.lineMap x y t₁)) (y - x) := by
    exact pos_of_mul_pos_right hsegment' (sub_pos.mpr ht12).le
  have hdiff :
      0 <
        deriv (fun t : ℝ ↦ J (AffineMap.lineMap x y t)) t₂ -
          deriv (fun t : ℝ ↦ J (AffineMap.lineMap x y t)) t₁ := by
    simpa [deriv_lineRestriction_eq_inner_gradient_sub J x y t₂ (hJ _ hz₂),
      deriv_lineRestriction_eq_inner_gradient_sub J x y t₁ (hJ _ hz₁)] using hdiffInner
  exact sub_pos.mp hdiff

/-- Convexity clause of Theorem 2.39. Suppose `J` is Fréchet differentiable on a convex set `C`.
Then `J` is convex on `C` if and only if
`0 ≤ inner ℝ (gradient J f1 - gradient J f2) (f1 - f2)` whenever `f1, f2 ∈ C`. -/
theorem convexOn_iff_inner_gradient_sub_nonneg (J : H → ℝ) {C : Set H}
    (hC : Convex ℝ C) (hJ : ∀ x ∈ C, DifferentiableAt ℝ J x) :
    ConvexOn ℝ C J ↔
      ∀ ⦃f1 f2 : H⦄, f1 ∈ C → f2 ∈ C →
        0 ≤ inner ℝ (gradient J f1 - gradient J f2) (f1 - f2) := by
  constructor
  · intro hconv f1 f2 hf1 hf2
    let g : ℝ → ℝ := J ∘ AffineMap.lineMap f2 f1
    -- Restrict the convex function to the segment from `f2` to `f1`.
    have hgConvex : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) g := by
      refine ⟨convex_Icc (0 : ℝ) 1, ?_⟩
      intro s hs t ht a b ha hb hab
      have hsC : AffineMap.lineMap f2 f1 s ∈ C := hC.lineMap_mem hf2 hf1 hs
      have htC : AffineMap.lineMap f2 f1 t ∈ C := hC.lineMap_mem hf2 hf1 ht
      have hcombo :
          AffineMap.lineMap f2 f1 (a * s + b * t) =
            a • AffineMap.lineMap f2 f1 s + b • AffineMap.lineMap f2 f1 t := by
        simpa [smul_eq_mul] using
          (Convex.combo_affine_apply (f := AffineMap.lineMap f2 f1) (x := s) (y := t) hab)
      simpa [g, Function.comp_def, hcombo] using hconv.2 hsC htC ha hb hab
    have hgDiff : ∀ t ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ g t := by
      intro t ht
      -- Differentiability of `J` along the segment gives differentiability of the 1D restriction.
      simpa [g, Function.comp_def] using (hJ _ (hC.lineMap_mem hf2 hf1 ht)).comp t
        (AffineMap.lineMap f2 f1).differentiableAt
    have hmonoDeriv : MonotoneOn (deriv g) (Set.Icc (0 : ℝ) 1) := hgConvex.monotoneOn_deriv hgDiff
    have h01 : deriv g 0 ≤ deriv g 1 := hmonoDeriv (by simp) (by simp) zero_le_one
    have hderiv0 : deriv g 0 = inner ℝ (gradient J f2) (f1 - f2) := by
      simpa [g, Function.comp_def] using
        deriv_lineRestriction_eq_inner_gradient_sub J f2 f1 0 (by simpa using hJ f2 hf2)
    have hderiv1 : deriv g 1 = inner ℝ (gradient J f1) (f1 - f2) := by
      simpa [g, Function.comp_def] using
        deriv_lineRestriction_eq_inner_gradient_sub J f2 f1 1 (by simpa using hJ f1 hf1)
    -- Endpoint monotonicity of the derivative is exactly the desired gradient inequality.
    have hinner :
        inner ℝ (gradient J f2) (f1 - f2) ≤ inner ℝ (gradient J f1) (f1 - f2) := by
      simpa [hderiv0, hderiv1] using h01
    simpa [inner_sub_left, sub_nonneg] using hinner
  · intro hmono
    have hmono' : GradientMonotoneOn J C := by
      rwa [gradientMonotoneOn_iff]
    refine ⟨hC, ?_⟩
    intro x hx y hy a b ha hb hab
    let g : ℝ → ℝ := J ∘ AffineMap.lineMap x y
    have hgDiff : ∀ t ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ g t := by
      intro t ht
      -- The line restriction is differentiable at each point of the closed interval.
      simpa [g, Function.comp_def] using (hJ _ (hC.lineMap_mem hx hy ht)).comp t
        (AffineMap.lineMap x y).differentiableAt
    have hgCont : ContinuousOn g (Set.Icc (0 : ℝ) 1) := by
      intro t ht
      exact (hgDiff t ht).continuousAt.continuousWithinAt
    have hgDiffInterior : DifferentiableOn ℝ g (interior (Set.Icc (0 : ℝ) 1)) := by
      intro t ht
      exact (hgDiff t (interior_subset ht)).differentiableWithinAt
    have hgDerivMono : MonotoneOn (deriv g) (interior (Set.Icc (0 : ℝ) 1)) := by
      intro s hs t ht hst
      have hs' : s ∈ Set.Ioo (0 : ℝ) 1 := by simpa [interior_Icc] using hs
      have ht' : t ∈ Set.Ioo (0 : ℝ) 1 := by simpa [interior_Icc] using ht
      simpa [g, Function.comp_def] using
        monotoneOnDeriv_lineRestriction_of_gradientMonotoneOn J hC hJ hmono' hx hy hs' ht' hst
    have hgConvex : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) g :=
      hgDerivMono.convexOn_of_deriv (convex_Icc (0 : ℝ) 1) hgCont hgDiffInterior
    have hseg : g (a • (0 : ℝ) + b • (1 : ℝ)) ≤ a • g 0 + b • g 1 := by
      exact hgConvex.2
        (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by simp)
        (show (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by simp)
        ha hb hab
    have hab' : 1 - b = a := by
      linarith
    -- Evaluate the convexity inequality for the segment restriction at the weight `b`.
    simpa [g, hab', AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one,
      AffineMap.lineMap_apply_module] using hseg

/-- Reusable `GradientMonotoneOn` form of the convexity clause in Theorem 2.39,
expressed using the predicate
`GradientMonotoneOn J C`. -/
theorem convexOn_iff_gradientMonotoneOn (J : H → ℝ) {C : Set H}
    (hC : Convex ℝ C) (hJ : ∀ x ∈ C, DifferentiableAt ℝ J x) :
    ConvexOn ℝ C J ↔ GradientMonotoneOn J C := by
  -- This is just the reusable predicate wrapper around the explicit inner-product inequality.
  simpa [gradientMonotoneOn_iff] using convexOn_iff_inner_gradient_sub_nonneg J hC hJ

/-- Strict-convexity clause of Theorem 2.39. Suppose `J` is Fréchet differentiable
on a convex set `C`.
Then `J` is strictly convex on `C` if and only if
`0 < inner ℝ (gradient J f1 - gradient J f2) (f1 - f2)` whenever
`f1, f2 ∈ C` and `f1 ≠ f2`. -/
theorem strictConvexOn_iff_inner_gradient_sub_pos (J : H → ℝ) {C : Set H}
    (hC : Convex ℝ C) (hJ : ∀ x ∈ C, DifferentiableAt ℝ J x) :
    StrictConvexOn ℝ C J ↔
      ∀ ⦃f1 f2 : H⦄, f1 ∈ C → f2 ∈ C → f1 ≠ f2 →
        0 < inner ℝ (gradient J f1 - gradient J f2) (f1 - f2) := by
  constructor
  · intro hconv f1 f2 hf1 hf2 hne
    let g : ℝ → ℝ := J ∘ AffineMap.lineMap f2 f1
    -- Restrict strict convexity to the nontrivial segment from `f2` to `f1`.
    have hgConvex : StrictConvexOn ℝ (Set.Icc (0 : ℝ) 1) g := by
      refine ⟨convex_Icc (0 : ℝ) 1, ?_⟩
      intro s hs t ht hst a b ha hb hab
      have hsC : AffineMap.lineMap f2 f1 s ∈ C := hC.lineMap_mem hf2 hf1 hs
      have htC : AffineMap.lineMap f2 f1 t ∈ C := hC.lineMap_mem hf2 hf1 ht
      have hlineNe : AffineMap.lineMap f2 f1 s ≠ AffineMap.lineMap f2 f1 t := by
        intro hEq
        exact hst ((AffineMap.lineMap_injective (k := ℝ) hne.symm) hEq)
      have hcombo :
          AffineMap.lineMap f2 f1 (a * s + b * t) =
            a • AffineMap.lineMap f2 f1 s + b • AffineMap.lineMap f2 f1 t := by
        simpa [smul_eq_mul] using
          (Convex.combo_affine_apply (f := AffineMap.lineMap f2 f1) (x := s) (y := t) hab)
      simpa [g, Function.comp_def, hcombo] using hconv.2 hsC htC hlineNe ha hb hab
    have hgDiff : ∀ t ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ g t := by
      intro t ht
      -- Differentiability of `J` along the segment makes the 1D restriction differentiable.
      simpa [g, Function.comp_def] using (hJ _ (hC.lineMap_mem hf2 hf1 ht)).comp t
        (AffineMap.lineMap f2 f1).differentiableAt
    have hmonoDeriv : StrictMonoOn (deriv g) (Set.Icc (0 : ℝ) 1) :=
      hgConvex.strictMonoOn_deriv hgDiff
    have h01 : deriv g 0 < deriv g 1 := hmonoDeriv (by simp) (by simp) zero_lt_one
    have hderiv0 : deriv g 0 = inner ℝ (gradient J f2) (f1 - f2) := by
      simpa [g, Function.comp_def] using
        deriv_lineRestriction_eq_inner_gradient_sub J f2 f1 0 (by simpa using hJ f2 hf2)
    have hderiv1 : deriv g 1 = inner ℝ (gradient J f1) (f1 - f2) := by
      simpa [g, Function.comp_def] using
        deriv_lineRestriction_eq_inner_gradient_sub J f2 f1 1 (by simpa using hJ f1 hf1)
    -- Strict endpoint growth of the derivative yields the strict gradient inequality.
    have hinner :
        inner ℝ (gradient J f2) (f1 - f2) < inner ℝ (gradient J f1) (f1 - f2) := by
      simpa [hderiv0, hderiv1] using h01
    simpa [inner_sub_left, sub_pos] using hinner
  · intro hmono
    have hmono' : GradientStrictMonotoneOn J C := by
      rwa [gradientStrictMonotoneOn_iff]
    refine ⟨hC, ?_⟩
    intro x hx y hy hxy a b ha hb hab
    let g : ℝ → ℝ := J ∘ AffineMap.lineMap x y
    have hgDiff : ∀ t ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ g t := by
      intro t ht
      -- Differentiability along the segment provides continuity of the restriction.
      simpa [g, Function.comp_def] using (hJ _ (hC.lineMap_mem hx hy ht)).comp t
        (AffineMap.lineMap x y).differentiableAt
    have hgCont : ContinuousOn g (Set.Icc (0 : ℝ) 1) := by
      intro t ht
      exact (hgDiff t ht).continuousAt.continuousWithinAt
    have hgDerivStrict : StrictMonoOn (deriv g) (interior (Set.Icc (0 : ℝ) 1)) := by
      intro s hs t ht hst
      have hs' : s ∈ Set.Ioo (0 : ℝ) 1 := by simpa [interior_Icc] using hs
      have ht' : t ∈ Set.Ioo (0 : ℝ) 1 := by simpa [interior_Icc] using ht
      simpa [g, Function.comp_def] using
        strictMonoOnDeriv_lineRestriction_of_gradientStrictMonotoneOn J hC hJ hmono' hx hy hxy
          hs' ht' hst
    have hgConvex : StrictConvexOn ℝ (Set.Icc (0 : ℝ) 1) g :=
      hgDerivStrict.strictConvexOn_of_deriv (convex_Icc (0 : ℝ) 1) hgCont
    have hseg : g (a • (0 : ℝ) + b • (1 : ℝ)) < a • g 0 + b • g 1 := by
      simpa using hgConvex.2 (by simp) (by simp) zero_ne_one ha hb hab
    have hab' : 1 - b = a := by
      linarith
    -- Translate the strict convexity inequality on `[0, 1]` back to the ambient segment.
    simpa [g, hab', AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one,
      AffineMap.lineMap_apply_module] using hseg

/-- Reusable `GradientStrictMonotoneOn` form of the strict-convexity clause in Theorem 2.39,
expressed using the predicate
`GradientStrictMonotoneOn J C`. -/
theorem strictConvexOn_iff_gradientStrictMonotoneOn (J : H → ℝ) {C : Set H}
    (hC : Convex ℝ C) (hJ : ∀ x ∈ C, DifferentiableAt ℝ J x) :
    StrictConvexOn ℝ C J ↔ GradientStrictMonotoneOn J C := by
  -- This is the reusable predicate wrapper around the explicit strict inner-product inequality.
  simpa [gradientStrictMonotoneOn_iff] using
    strictConvexOn_iff_inner_gradient_sub_pos J hC hJ

/-- Theorem 2.39. The label `thm_2_39` records that if `J` is Fréchet differentiable on a convex
set `C`. Then `J` is convex on `C` if and only if
`0 ≤ inner ℝ (gradient J f1 - gradient J f2) (f1 - f2)` whenever `f1, f2 ∈ C`.
Also, `J` is strictly convex on `C` if and only if the same inequality is
strict whenever `f1 ≠ f2`. -/
theorem convexAndStrictConvexOn_iff_gradientMonotonicityOn (J : H → ℝ) {C : Set H}
    (hC : Convex ℝ C) (hJ : ∀ x ∈ C, DifferentiableAt ℝ J x) :
    (ConvexOn ℝ C J ↔
      ∀ ⦃f1 f2 : H⦄, f1 ∈ C → f2 ∈ C →
        0 ≤ inner ℝ (gradient J f1 - gradient J f2) (f1 - f2)) ∧
      (StrictConvexOn ℝ C J ↔
        ∀ ⦃f1 f2 : H⦄, f1 ∈ C → f2 ∈ C → f1 ≠ f2 →
          0 < inner ℝ (gradient J f1 - gradient J f2) (f1 - f2)) := by
  -- Assemble the convex and strict-convex clauses from the two established equivalences.
  exact ⟨convexOn_iff_inner_gradient_sub_nonneg J hC hJ,
    strictConvexOn_iff_inner_gradient_sub_pos J hC hJ⟩

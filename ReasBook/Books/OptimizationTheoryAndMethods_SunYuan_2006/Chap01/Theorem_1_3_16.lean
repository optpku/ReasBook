/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Strong
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_3_15
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Theorem_1_3_13

-- Domain-style sampling for this item:
-- * core/canonical owners: `ConvexOn`, `StrictConvexOn`, `StrongConvexOn`;
-- * source-facing owner: `monotoneOperatorOn` from Definition 1.3.15;
-- * Chapter 1 precedent: Theorem 1.3.13 already states the gradient criteria on the canonical
--   complete real inner-product-space ambient layer, so this file should not stay pinned to the
--   coordinate model `EuclideanSpace ℝ (Fin n)`.

section Theorem1316

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {D S : Set E} {f : E → ℝ}
variable (hD_open : IsOpen D) (hSD : S ⊆ D) (hS_convex : Convex ℝ S)
variable (hf : DifferentiableOn ℝ f D)

/-- Helper for Chapter01 Theorem 1.3.16: the derivative of the line restriction
`t ↦ f (lineMap x y t)` is the directional derivative given by the gradient. -/
lemma hasDerivAt_lineMap_comp
    (hD_open : IsOpen D) (hf : DifferentiableOn ℝ f D)
    {x y : E} {t : ℝ} (ht : AffineMap.lineMap x y t ∈ D) :
    HasDerivAt (fun s : ℝ ↦ f (AffineMap.lineMap x y s))
      (inner ℝ (gradient f (AffineMap.lineMap x y t)) (y - x)) t := by
  -- Route correction: isolate the chain-rule normalization on the line restriction before using it
  -- in the convexity equivalences.
  have hgrad : HasGradientAt f (gradient f (AffineMap.lineMap x y t)) (AffineMap.lineMap x y t) :=
    ((hf _ ht).differentiableAt (hD_open.mem_nhds ht)).hasGradientAt
  -- Rewrite the goal into the exact composition shape produced by the chain rule.
  change HasDerivAt (f ∘ (AffineMap.lineMap x y : ℝ → E))
    (inner ℝ (gradient f (AffineMap.lineMap x y t)) (y - x)) t
  simpa using
    (hgrad.hasFDerivAt.comp_hasDerivAt_of_eq
      (hf := AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := t))
      (hy := rfl))

/-- Helper for Chapter01 Theorem 1.3.16: evaluating the derivative of the line restriction gives
the inner product of the gradient with the segment direction. -/
lemma deriv_lineMap_comp
    (hD_open : IsOpen D) (hf : DifferentiableOn ℝ f D)
    {x y : E} {t : ℝ} (ht : AffineMap.lineMap x y t ∈ D) :
    deriv (fun s : ℝ ↦ f (AffineMap.lineMap x y s)) t =
      inner ℝ (gradient f (AffineMap.lineMap x y t)) (y - x) := by
  -- Read the scalar derivative off the line-restriction `HasDerivAt` formula.
  simpa using (hasDerivAt_lineMap_comp (D := D) (f := f) hD_open hf ht).deriv

/-- Helper for Chapter01 Theorem 1.3.16: the displacement between two points on the same affine
line is the parameter difference times the direction vector. -/
lemma lineMap_sub_eq_smul_sub {x y : E} {s t : ℝ} :
    AffineMap.lineMap x y t - AffineMap.lineMap x y s = (t - s) • (y - x) := by
  -- Expand both affine points from the same base point `x`, then collect the direction terms.
  calc
    AffineMap.lineMap x y t - AffineMap.lineMap x y s
        = (t • (y - x) + x) - (s • (y - x) + x) := by
            rw [AffineMap.lineMap_apply_module', AffineMap.lineMap_apply_module']
    _ = t • (y - x) - s • (y - x) := by
          abel_nf
    _ = (t - s) • (y - x) := by
          rw [sub_smul]

/-- Helper for Chapter01 Theorem 1.3.16: every point on the unit-interval line segment joining
`x` and `y` stays in the convex set `S`. -/
lemma lineMap_mem_of_mem_unitInterval
    (hS_convex : Convex ℝ S) {x y : E} (hx : x ∈ S) (hy : y ∈ S) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    AffineMap.lineMap x y t ∈ S := by
  -- Rewrite the affine point as a convex combination and apply convexity of `S`.
  rw [AffineMap.lineMap_apply_module]
  exact hS_convex hx hy (sub_nonneg.2 ht.2) ht.1 (by linarith)

/-- Helper for Chapter01 Theorem 1.3.16: the whole unit-interval line segment joining points of
`S` lies in the ambient open differentiability domain `D`. -/
lemma lineMap_mem_D_of_mem_unitInterval
    (hSD : S ⊆ D) (hS_convex : Convex ℝ S) {x y : E} (hx : x ∈ S) (hy : y ∈ S) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    AffineMap.lineMap x y t ∈ D :=
  hSD (lineMap_mem_of_mem_unitInterval (S := S) hS_convex hx hy ht)

/-- Helper for Chapter01 Theorem 1.3.16: convexity on `S ⊆ D` still gives the first-order
support inequality at points of `S` because the supporting-line argument only needs
differentiability on the ambient open set containing the segment. -/
lemma ge_gradient_inner_sub_of_convexOn_subset_open
    (hD_open : IsOpen D) (hSD : S ⊆ D) (hS_convex : Convex ℝ S)
    (hconv : ConvexOn ℝ S f) (hf : DifferentiableOn ℝ f D)
    {x y : E} (hx : x ∈ S) (hy : y ∈ S) :
    f y ≥ f x + inner ℝ (gradient f x) (y - x) := by
  let g : ℝ → ℝ := fun t ↦ f (AffineMap.lineMap x y t)
  have hpre : ConvexOn ℝ ((AffineMap.lineMap x y) ⁻¹' S) g := by
    have hpre' : ConvexOn ℝ ((AffineMap.lineMap x y) ⁻¹' S) (f ∘ AffineMap.lineMap x y) :=
      hconv.comp_affineMap (AffineMap.lineMap x y)
    simpa [g]
  have hgconv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) g := by
    refine hpre.subset ?_ (convex_Icc (0 : ℝ) 1)
    intro t ht
    exact lineMap_mem_of_mem_unitInterval (S := S) hS_convex hx hy ht
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by simp
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by simp
  have hderiv_g : HasDerivAt g (inner ℝ (gradient f x) (y - x)) 0 := by
    -- Read the endpoint derivative of the line restriction directly from the chain rule.
    simpa [g] using
      hasDerivAt_lineMap_comp (D := D) (f := f) hD_open hf
        (lineMap_mem_D_of_mem_unitInterval
          (D := D) (S := S) hSD hS_convex hx hy h0)
  have hslope : inner ℝ (gradient f x) (y - x) ≤ f y - f x := by
    -- Convexity of the restricted one-variable function compares the derivative at `0`
    -- with the slope between `0` and `1`.
    have h' := hgconv.deriv_le_slope h0 h1 zero_lt_one hderiv_g.differentiableAt
    rw [hderiv_g.deriv] at h'
    simpa [g, slope_def_field] using h'
  linarith

/-- Helper for Chapter01 Theorem 1.3.16: the source mean-value-theorem proof turns monotonicity
of the gradient on `S` into the first-order support inequality on `S`. -/
lemma ge_gradient_inner_sub_of_monotoneOperatorOn
    (hD_open : IsOpen D) (hSD : S ⊆ D) (hS_convex : Convex ℝ S)
    (hf : DifferentiableOn ℝ f D)
    (hmono : monotoneOperatorOn (fun x : S ↦ gradient f x) Set.univ)
    {x y : E} (hx : x ∈ S) (hy : y ∈ S) :
    f y ≥ f x + inner ℝ (gradient f x) (y - x) := by
  -- Route correction: use the textbook mean-value theorem point on the segment, rather than the
  -- stalled global package for monotonicity of the whole restricted derivative.
  let g : ℝ → ℝ := fun t ↦ f (AffineMap.lineMap x y t)
  have hgcont : ContinuousOn g (Set.Icc (0 : ℝ) 1) := by
    intro t ht
    exact
      ((hasDerivAt_lineMap_comp (D := D) (f := f) hD_open hf
          (lineMap_mem_D_of_mem_unitInterval
            (D := D) (S := S) hSD hS_convex hx hy ht)).continuousAt).continuousWithinAt
  have hgdiff : DifferentiableOn ℝ g (Set.Ioo (0 : ℝ) 1) := by
    intro t ht
    have hdt :=
      (hasDerivAt_lineMap_comp (D := D) (f := f) hD_open hf
        (lineMap_mem_D_of_mem_unitInterval
          (D := D) (S := S) hSD hS_convex hx hy ⟨ht.1.le, ht.2.le⟩)).differentiableAt
    exact hdt.differentiableWithinAt
  obtain ⟨t, ht, hmvt⟩ := exists_deriv_eq_slope g zero_lt_one hgcont hgdiff
  let ξ : E := AffineMap.lineMap x y t
  have hξS : ξ ∈ S := by
    exact lineMap_mem_of_mem_unitInterval (S := S) hS_convex hx hy ⟨ht.1.le, ht.2.le⟩
  have hξD : ξ ∈ D := hSD hξS
  have hmono_seg : 0 ≤ inner ℝ (gradient f ξ - gradient f x) (ξ - x) := by
    let ξS : S := ⟨ξ, hξS⟩
    let xS : S := ⟨x, hx⟩
    simpa [ξ, ξS, xS] using hmono (x := ξS) (y := xS) (by simp) (by simp)
  have hξsub : ξ - x = t • (y - x) := by
    -- The mean-value point lies on the same line segment, so its displacement from `x`
    -- is a positive scalar multiple of `y - x`.
    simpa [ξ, AffineMap.lineMap_apply_zero] using
      (lineMap_sub_eq_smul_sub (x := x) (y := y) (s := (0 : ℝ)) (t := t))
  have hmono_dir : 0 ≤ inner ℝ (gradient f ξ - gradient f x) (y - x) := by
    rw [hξsub, real_inner_smul_right] at hmono_seg
    by_contra hneg
    have hlt : t * inner ℝ (gradient f ξ - gradient f x) (y - x) < 0 := by
      exact mul_neg_of_pos_of_neg ht.1 (lt_of_not_ge hneg)
    exact (not_lt_of_ge hmono_seg) hlt
  have hmvt' : f y - f x = inner ℝ (gradient f ξ) (y - x) := by
    -- The derivative supplied by the mean value theorem is exactly the directional derivative
    -- along the segment.
    calc
      f y - f x = deriv g t := by
        symm
        simpa [g, slope_def_field] using hmvt
      _ = inner ℝ (gradient f ξ) (y - x) := by
        simpa [g, ξ] using deriv_lineMap_comp (D := D) (f := f) hD_open hf hξD
  have hsplit :
      inner ℝ (gradient f ξ - gradient f x) (y - x) =
        inner ℝ (gradient f ξ) (y - x) - inner ℝ (gradient f x) (y - x) := by
    rw [inner_sub_left]
  rw [hsplit] at hmono_dir
  linarith

/-- Helper for Chapter01 Theorem 1.3.16: strict convexity on `S ⊆ D` gives the strict
first-order support inequality on `S` by the same midpoint argument as Theorem 1.3.13. -/
lemma gt_gradient_inner_sub_of_strictConvexOn_subset_open
    (hD_open : IsOpen D) (hSD : S ⊆ D) (hS_convex : Convex ℝ S)
    (hstrict : StrictConvexOn ℝ S f) (hf : DifferentiableOn ℝ f D)
    {x y : E} (hx : x ∈ S) (hy : y ∈ S) (hyx : y ≠ x) :
    f y > f x + inner ℝ (gradient f x) (y - x) := by
  let z := (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y
  have hz : z ∈ S := hS_convex hx hy (by positivity) (by positivity) (by ring)
  have hmid : f z < (1 / 2 : ℝ) * f x + (1 / 2 : ℝ) * f y := by
    -- Strict convexity at the midpoint provides the strict gap.
    simpa [z, smul_eq_mul, add_comm, add_left_comm, add_assoc] using
      hstrict.2 hx hy hyx.symm (by positivity) (by positivity) (by ring)
  have hsupport : f z ≥ f x + inner ℝ (gradient f x) (z - x) := by
    -- The ambient-open support inequality handles the non-strict piece.
    exact ge_gradient_inner_sub_of_convexOn_subset_open
      (D := D) (S := S) (f := f) hD_open hSD hS_convex hstrict.convexOn hf hx hz
  have hzsub : z - x = (1 / 2 : ℝ) • (y - x) := by
    -- Rewrite the midpoint displacement into the segment direction.
    have hzline : z = AffineMap.lineMap x y (1 / 2 : ℝ) := by
      dsimp [z]
      rw [AffineMap.lineMap_apply_module]
      norm_num
    calc
      z - x = AffineMap.lineMap x y (1 / 2 : ℝ) - x := by rw [hzline]
      _ = (1 / 2 : ℝ) • (y - x) := by
        simp [AffineMap.lineMap_apply_module', sub_eq_add_neg, add_comm]
  have hsupport' : f x + (1 / 2 : ℝ) * inner ℝ (gradient f x) (y - x) ≤ f z := by
    have hsupport'' : f x + inner ℝ (gradient f x) (z - x) ≤ f z := by linarith
    rw [hzsub, real_inner_smul_right] at hsupport''
    exact hsupport''
  linarith

/-- Helper for Chapter01 Theorem 1.3.16: the strict support inequality already implies strict
convexity once `S` is convex, so the reverse direction needs no extra openness assumption. -/
lemma strictConvexOn_of_gt_gradient_inner_sub
    (hS_convex : Convex ℝ S)
    (hgrad :
      ∀ x ∈ S, ∀ y ∈ S, y ≠ x →
        f y > f x + inner ℝ (gradient f x) (y - x)) :
    StrictConvexOn ℝ S f := by
  refine ⟨hS_convex, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  let z := a • x + b • y
  have hz : z ∈ S := hS_convex hx hy ha.le hb.le hab
  have hzx : x ≠ z := by
    have hba : b = 1 - a := by linarith
    have hzline : z = AffineMap.lineMap y x a := by
      simp [z, AffineMap.lineMap_apply_module, hba, add_comm]
    intro hzx
    rw [hzline] at hzx
    rcases (AffineMap.lineMap_eq_right_iff (p₀ := y) (p₁ := x) (c := a)).1 hzx.symm with h' | h'
    · exact hxy h'.symm
    · linarith
  have hzy : y ≠ z := by
    have hab' : a = 1 - b := by linarith
    have hzline : z = AffineMap.lineMap x y b := by
      simp [z, AffineMap.lineMap_apply_module, hab', add_comm]
    intro hzy
    rw [hzline] at hzy
    rcases (AffineMap.lineMap_eq_right_iff (p₀ := x) (p₁ := y) (c := b)).1 hzy.symm with h' | h'
    · exact hxy h'
    · linarith
  have hx_support := hgrad z hz x hx hzx
  have hy_support := hgrad z hz y hy hzy
  have hx_mul : a * (f z + inner ℝ (gradient f z) (x - z)) < a * f x :=
    mul_lt_mul_of_pos_left hx_support ha
  have hy_mul : b * (f z + inner ℝ (gradient f z) (y - z)) < b * f y :=
    mul_lt_mul_of_pos_left hy_support hb
  have hcancel_vec : a • (x - z) + b • (y - z) = 0 := by
    -- The weighted displacement from the base point `z` still cancels exactly.
    calc
      a • (x - z) + b • (y - z) = (a • x + b • y) - (a • z + b • z) := by
        rw [smul_sub, smul_sub]
        abel_nf
      _ = (a • x + b • y) - z := by
        rw [← add_smul, hab, one_smul]
      _ = z - z := by rfl
      _ = 0 := sub_self z
  have hcancel :
      a * inner ℝ (gradient f z) (x - z) + b * inner ℝ (gradient f z) (y - z) = 0 := by
    -- Linearize the inner product to remove the gradient term by `hcancel_vec`.
    calc
      a * inner ℝ (gradient f z) (x - z) + b * inner ℝ (gradient f z) (y - z)
          = inner ℝ (gradient f z) (a • (x - z) + b • (y - z)) := by
              rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
      _ = inner ℝ (gradient f z) 0 := by rw [hcancel_vec]
      _ = 0 := by simp
  have hsum : a * (f z + inner ℝ (gradient f z) (x - z)) +
      b * (f z + inner ℝ (gradient f z) (y - z)) < a * f x + b * f y :=
    add_lt_add hx_mul hy_mul
  have hleft :
      a * (f z + inner ℝ (gradient f z) (x - z)) +
        b * (f z + inner ℝ (gradient f z) (y - z)) = f z := by
    calc
      a * (f z + inner ℝ (gradient f z) (x - z)) +
          b * (f z + inner ℝ (gradient f z) (y - z))
          = (a + b) * f z +
              (a * inner ℝ (gradient f z) (x - z) +
                b * inner ℝ (gradient f z) (y - z)) := by ring
      _ = f z + 0 := by rw [hab, one_mul, hcancel]
      _ = f z := by ring
  simpa [z, smul_eq_mul] using hleft ▸ hsum

/-- Helper for Chapter01 Theorem 1.3.16: the source mean-value-theorem proof upgrades strict
monotonicity of the gradient on `S` to the strict first-order support inequality. -/
lemma gt_gradient_inner_sub_of_strictlyMonotoneOperatorOn
    (hD_open : IsOpen D) (hSD : S ⊆ D) (hS_convex : Convex ℝ S)
    (hf : DifferentiableOn ℝ f D)
    (hmono : strictlyMonotoneOperatorOn (fun x : S ↦ gradient f x) Set.univ)
    {x y : E} (hx : x ∈ S) (hy : y ∈ S) (hyx : y ≠ x) :
    f y > f x + inner ℝ (gradient f x) (y - x) := by
  -- Route correction: keep the source argument at the single mean-value point `ξ`
  -- instead of proving a stronger global statement about the whole restricted derivative.
  let g : ℝ → ℝ := fun t ↦ f (AffineMap.lineMap x y t)
  have hgcont : ContinuousOn g (Set.Icc (0 : ℝ) 1) := by
    intro t ht
    exact
      ((hasDerivAt_lineMap_comp (D := D) (f := f) hD_open hf
          (lineMap_mem_D_of_mem_unitInterval
            (D := D) (S := S) hSD hS_convex hx hy ht)).continuousAt).continuousWithinAt
  have hgdiff : DifferentiableOn ℝ g (Set.Ioo (0 : ℝ) 1) := by
    intro t ht
    have hdt :=
      (hasDerivAt_lineMap_comp (D := D) (f := f) hD_open hf
        (lineMap_mem_D_of_mem_unitInterval
          (D := D) (S := S) hSD hS_convex hx hy ⟨ht.1.le, ht.2.le⟩)).differentiableAt
    exact hdt.differentiableWithinAt
  obtain ⟨t, ht, hmvt⟩ := exists_deriv_eq_slope g zero_lt_one hgcont hgdiff
  let ξ : E := AffineMap.lineMap x y t
  have hξS : ξ ∈ S := by
    exact lineMap_mem_of_mem_unitInterval (S := S) hS_convex hx hy ⟨ht.1.le, ht.2.le⟩
  have hξD : ξ ∈ D := hSD hξS
  have hξne : ξ ≠ x := by
    -- Interior points of the segment are distinct from the left endpoint when `x ≠ y`.
    intro hξx
    rcases (AffineMap.lineMap_eq_left_iff (p₀ := x) (p₁ := y) (c := t)).1 hξx with hxy | ht0
    · exact hyx hxy.symm
    · exact (ne_of_gt ht.1) ht0
  have hmono_seg : 0 < inner ℝ (gradient f ξ - gradient f x) (ξ - x) := by
    let ξS : S := ⟨ξ, hξS⟩
    let xS : S := ⟨x, hx⟩
    have hξSne : ξS ≠ xS := by
      intro hEq
      exact hξne (congrArg Subtype.val hEq)
    simpa [ξ, ξS, xS] using hmono (x := ξS) (y := xS) (by simp) (by simp) hξSne
  have hξsub : ξ - x = t • (y - x) := by
    -- The displacement from `x` to the mean-value point is still a positive multiple of `y - x`.
    simpa [ξ, AffineMap.lineMap_apply_zero] using
      (lineMap_sub_eq_smul_sub (x := x) (y := y) (s := (0 : ℝ)) (t := t))
  have hmono_dir : 0 < inner ℝ (gradient f ξ - gradient f x) (y - x) := by
    rw [hξsub, real_inner_smul_right] at hmono_seg
    by_contra hnonpos
    have hle : inner ℝ (gradient f ξ - gradient f x) (y - x) ≤ 0 := le_of_not_gt hnonpos
    have hnonpos_mul : t * inner ℝ (gradient f ξ - gradient f x) (y - x) ≤ 0 := by
      exact mul_nonpos_of_nonneg_of_nonpos ht.1.le hle
    exact not_le_of_gt hmono_seg hnonpos_mul
  have hmvt' : f y - f x = inner ℝ (gradient f ξ) (y - x) := by
    -- Replace the slope from the mean value theorem by the directional derivative at `ξ`.
    calc
      f y - f x = deriv g t := by
        symm
        simpa [g, slope_def_field] using hmvt
      _ = inner ℝ (gradient f ξ) (y - x) := by
        simpa [g, ξ] using deriv_lineMap_comp (D := D) (f := f) hD_open hf hξD
  have hsplit :
      inner ℝ (gradient f ξ - gradient f x) (y - x) =
        inner ℝ (gradient f ξ) (y - x) - inner ℝ (gradient f x) (y - x) := by
    rw [inner_sub_left]
  rw [hsplit] at hmono_dir
  linarith

/-- Helper for Chapter01 Theorem 1.3.16: subtracting `c • x` from the gradient converts strong
monotonicity into ordinary monotonicity of the shifted gradient. -/
lemma monotoneOperatorOn_gradient_sub_smul_iff_strong_ineq (c : ℝ) :
    monotoneOperatorOn (fun x : S ↦ gradient f x - c • (x : E)) Set.univ ↔
      ∀ x y : S,
        inner ℝ (gradient f x - gradient f y) ((x : E) - y) ≥
          c * ‖(x : E) - y‖ ^ (2 : ℕ) := by
  constructor
  · intro h x y
    have hxy := h (x := x) (y := y) (by simp) (by simp)
    have hrewrite :
        inner ℝ ((gradient f x - c • (x : E)) - (gradient f y - c • (y : E))) ((x : E) - y) =
          inner ℝ (gradient f x - gradient f y) ((x : E) - y) -
            c * ‖(x : E) - y‖ ^ (2 : ℕ) := by
      -- Move the quadratic term to the right-hand side so the inequality matches the source form.
      calc
        inner ℝ ((gradient f x - c • (x : E)) - (gradient f y - c • (y : E))) ((x : E) - y)
            = inner ℝ ((gradient f x - gradient f y) - c • ((x : E) - y)) ((x : E) - y) := by
                congr 1
                rw [smul_sub]
                abel_nf
        _ = inner ℝ (gradient f x - gradient f y) ((x : E) - y) -
              inner ℝ (c • ((x : E) - y)) ((x : E) - y) := by
                rw [inner_sub_left]
        _ = inner ℝ (gradient f x - gradient f y) ((x : E) - y) -
              c * ‖(x : E) - y‖ ^ (2 : ℕ) := by
                rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
    rw [hrewrite] at hxy
    linarith
  · intro h
    intro x y hx hy
    have hxy := h x y
    have hrewrite :
        inner ℝ ((gradient f x - c • (x : E)) - (gradient f y - c • (y : E))) ((x : E) - y) =
          inner ℝ (gradient f x - gradient f y) ((x : E) - y) -
            c * ‖(x : E) - y‖ ^ (2 : ℕ) := by
      -- Use the same canonical normalization in the reverse direction.
      calc
        inner ℝ ((gradient f x - c • (x : E)) - (gradient f y - c • (y : E))) ((x : E) - y)
            = inner ℝ ((gradient f x - gradient f y) - c • ((x : E) - y)) ((x : E) - y) := by
                congr 1
                rw [smul_sub]
                abel_nf
        _ = inner ℝ (gradient f x - gradient f y) ((x : E) - y) -
              inner ℝ (c • ((x : E) - y)) ((x : E) - y) := by
                rw [inner_sub_left]
        _ = inner ℝ (gradient f x - gradient f y) ((x : E) - y) -
              c * ‖(x : E) - y‖ ^ (2 : ℕ) := by
                rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
    rw [hrewrite]
    linarith

/-- Chapter01 Theorem 1.3.16 (1): let `D` be open in a real inner product space, let `S ⊆ D` be
convex, and let `f : E → ℝ` be differentiable on `D`. Then `f` is convex on `S` if and only if
its gradient is monotone on `S`, i.e. `inner ℝ (gradient f x - gradient f y) (x - y) ≥ 0` for
all `x, y ∈ S`. The source statement on `ℝ^n` is the corresponding specialization. -/
theorem convexOn_iff_gradient_monotoneOn
    (hD_open : IsOpen D) (hSD : S ⊆ D) (hS_convex : Convex ℝ S)
    (hf : DifferentiableOn ℝ f D)
    :
    ConvexOn ℝ S f ↔
      monotoneOperatorOn (fun x : S ↦ gradient f x) Set.univ := by
  constructor
  · intro hconv
    intro x y hx hy
    -- Add the two supporting inequalities from `x` to `y` and from `y` to `x`.
    have hxy :=
      ge_gradient_inner_sub_of_convexOn_subset_open
        (D := D) (S := S) (f := f) hD_open hSD hS_convex hconv hf x.2 y.2
    have hyx :=
      ge_gradient_inner_sub_of_convexOn_subset_open
        (D := D) (S := S) (f := f) hD_open hSD hS_convex hconv hf y.2 x.2
    have hxy' := hxy
    have hsub : ((y : E) - x) = - (((x : E) - y)) := by
      abel_nf
    rw [hsub, inner_neg_right] at hxy'
    rw [inner_sub_left]
    linarith
  · intro hmono
    -- The source MVT bridge yields the support inequality, and Theorem 1.3.13 closes convexity.
    refine convexOn_of_ge_gradient_inner_sub hS_convex ?_
    intro x hx y hy
    exact
      ge_gradient_inner_sub_of_monotoneOperatorOn
        (D := D) (S := S) (f := f) hD_open hSD hS_convex hf hmono hx hy

/-- Chapter01 Theorem 1.3.16 (2): under the same hypotheses, `f` is strictly convex on `S` if
and only if its gradient is strictly monotone on `S`, i.e.
`inner ℝ (gradient f x - gradient f y) (x - y) > 0` for all distinct `x, y ∈ S`. -/
theorem strictConvexOn_iff_gradient_strictMonotoneOn
    (hD_open : IsOpen D) (hSD : S ⊆ D) (hS_convex : Convex ℝ S)
    (hf : DifferentiableOn ℝ f D)
    :
    StrictConvexOn ℝ S f ↔
      strictlyMonotoneOperatorOn (fun x : S ↦ gradient f x) Set.univ := by
  constructor
  · intro hstrict
    intro x y hx hy hxy
    have hyxE : (y : E) ≠ x := by
      intro hEq
      exact hxy (Subtype.ext hEq.symm)
    have hxyE : (x : E) ≠ y := by
      intro hEq
      exact hxy (Subtype.ext hEq)
    -- Add the two strict supporting inequalities from the source proof.
    have hxy_support :=
      gt_gradient_inner_sub_of_strictConvexOn_subset_open
        (D := D) (S := S) (f := f) hD_open hSD hS_convex hstrict hf x.2 y.2 hyxE
    have hyx_support :=
      gt_gradient_inner_sub_of_strictConvexOn_subset_open
        (D := D) (S := S) (f := f) hD_open hSD hS_convex hstrict hf y.2 x.2 hxyE
    have hxy_support' := hxy_support
    have hsub : ((y : E) - x) = - (((x : E) - y)) := by
      abel_nf
    rw [hsub, inner_neg_right] at hxy_support'
    rw [inner_sub_left]
    linarith
  · intro hmono
    -- The strict MVT bridge gives strict support, and the weighted-sum argument closes strict
    -- convexity without any extra openness on `S`.
    refine strictConvexOn_of_gt_gradient_inner_sub hS_convex ?_
    intro x hx y hy hyx
    exact
      gt_gradient_inner_sub_of_strictlyMonotoneOperatorOn
        (D := D) (S := S) (f := f) hD_open hSD hS_convex hf hmono hx hy hyx

/-- Chapter01 Theorem 1.3.16 (3): under the same hypotheses, `f` is uniformly, equivalently
strongly, convex on `S` if and only if there exists `c > 0` such that
`inner ℝ (gradient f x - gradient f y) (x - y) ≥ c * ‖x - y‖^2` for all `x, y ∈ S`. -/
theorem exists_strongConvexOn_iff_gradient_strongMonotoneOn
    (hD_open : IsOpen D) (hSD : S ⊆ D) (hS_convex : Convex ℝ S)
    (hf : DifferentiableOn ℝ f D)
    :
    (∃ c > 0, StrongConvexOn S c f) ↔
      stronglyMonotoneOperatorOn (fun x : S ↦ gradient f x) Set.univ := by
  constructor
  · rintro ⟨c, hc, hstrong⟩
    let gfun : E → ℝ := fun z ↦ f z - (c / 2) * ‖z‖ ^ (2 : ℕ)
    have hgdiff : DifferentiableOn ℝ gfun D := by
      intro z hz
      have hfz : HasGradientAt f (gradient f z) z :=
        ((hf z hz).differentiableAt (hD_open.mem_nhds hz)).hasGradientAt
      exact (hasGradientAt_sub_half_mul_norm_sq (c := c) hfz).differentiableAt.differentiableWithinAt
    have hgconv : ConvexOn ℝ S gfun := (strongConvexOn_iff_convex).1 hstrong
    have hgmono :
        monotoneOperatorOn (fun x : S ↦ gradient gfun x) Set.univ :=
      (convexOn_iff_gradient_monotoneOn (D := D) (S := S) (f := gfun)
        hD_open hSD hS_convex hgdiff).1 hgconv
    have hgrad_shift :
        (fun x : S ↦ gradient gfun x) = fun x : S ↦ gradient f x - c • (x : E) := by
      funext x
      have hfx : HasGradientAt f (gradient f x) x :=
        ((hf x (hSD x.2)).differentiableAt (hD_open.mem_nhds (hSD x.2))).hasGradientAt
      exact (hasGradientAt_sub_half_mul_norm_sq (c := c) hfx).gradient
    have hshift_mono :
        monotoneOperatorOn (fun x : S ↦ gradient f x - c • (x : E)) Set.univ := by
      rw [← hgrad_shift]
      exact hgmono
    rw [stronglyMonotoneOperatorOn_iff]
    refine ⟨c, hc, ?_⟩
    intro x y hx hy
    exact (monotoneOperatorOn_gradient_sub_smul_iff_strong_ineq
      (S := S) (f := f) c).1 hshift_mono x y
  · rw [stronglyMonotoneOperatorOn_iff]
    rintro ⟨c, hc, hmono⟩
    let gfun : E → ℝ := fun z ↦ f z - (c / 2) * ‖z‖ ^ (2 : ℕ)
    have hgdiff : DifferentiableOn ℝ gfun D := by
      intro z hz
      have hfz : HasGradientAt f (gradient f z) z :=
        ((hf z hz).differentiableAt (hD_open.mem_nhds hz)).hasGradientAt
      exact (hasGradientAt_sub_half_mul_norm_sq (c := c) hfz).differentiableAt.differentiableWithinAt
    have hshift_mono :
        monotoneOperatorOn (fun x : S ↦ gradient f x - c • (x : E)) Set.univ :=
      (monotoneOperatorOn_gradient_sub_smul_iff_strong_ineq
        (S := S) (f := f) c).2 (fun x y ↦ hmono (by simp) (by simp))
    have hgrad_shift :
        (fun x : S ↦ gradient gfun x) = fun x : S ↦ gradient f x - c • (x : E) := by
      funext x
      have hfx : HasGradientAt f (gradient f x) x :=
        ((hf x (hSD x.2)).differentiableAt (hD_open.mem_nhds (hSD x.2))).hasGradientAt
      exact (hasGradientAt_sub_half_mul_norm_sq (c := c) hfx).gradient
    have hgmono :
        monotoneOperatorOn (fun x : S ↦ gradient gfun x) Set.univ := by
      rw [hgrad_shift]
      exact hshift_mono
    have hgconv : ConvexOn ℝ S gfun :=
      (convexOn_iff_gradient_monotoneOn (D := D) (S := S) (f := gfun)
        hD_open hSD hS_convex hgdiff).2 hgmono
    exact ⟨c, hc, (strongConvexOn_iff_convex).2 hgconv⟩

end Theorem1316

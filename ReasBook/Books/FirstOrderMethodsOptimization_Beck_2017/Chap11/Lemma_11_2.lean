/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Lemma_5_7
import FirstOrderMethodsOptimization_Beck_2017.Chap11.Definition_11_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

section

variable {ι : Type u} {Ei : ι → Type v}
variable [∀ i, NormedAddCommGroup (Ei i)] [∀ i, InnerProductSpace ℝ (Ei i)]

/- Domain sampling for this refinement:
- Chapter 5's `is_l_smooth_on` is the owner predicate for quadratic upper models on convex sets.
- `𝒰[i]` and `block_coordinate_slice` from `Definition_11_4` are the canonical one-block update
  and frozen-slice owners.
- `IsBlockProximalGradientProblem.block_partial_gradient_hasGradientAt` is the owner-level bridge
  from the Chapter 11 block-gradient data to the gradient of the one-block slice.

Lemma 11.2 is `source-facing`: it is the one-block quadratic upper model along the textbook update
`x + 𝒰[i] d`. Its best `core/canonical` owner for the labeled chapter statement is
`BlockProximalGradientAssumptions`, while the lower-level Chapter 5 invocation remains a
`bridge/view` theorem with explicit slice smoothness data. The primitive data for that bridge are
only the chosen block `i`, its smoothness constant, the slice smoothness owner, and the block
gradient at the base point; under the Chapter 11 owner these are all derived. -/

-- Proof sketch: apply the Chapter 5 descent lemma to the fixed one-block slice
-- `block_coordinate_slice f x i : Ei i → ℝ` on the admissible block set
-- `{d | x + 𝒰[i] d ∈ interior (effective_domain f)}`. Convexity of that slice
-- domain is assumed
-- directly, the owner hypothesis `h_slice_smooth` supplies the smoothness input, and the
-- gradient specification at `0` identifies the linear term with
-- `block_gradient i x`.
/-- Bridge lemma for Lemma 11.2: fix a block index `i` and a base point `x`, and suppose the
admissible one-block slice domain
`{d | x + 𝒰[i] d ∈ interior (effective_domain f)}` is convex. If the `i`-th
slice `d ↦ f (x + 𝒰[i] d)` is `L`-smooth on that admissible slice domain and has gradient
`block_gradient i x` at `d = 0`, then the block update satisfies the quadratic upper model
`f (x + 𝒰[i] d) ≤ f x + ⟪block_gradient i x, d⟫ + (L / 2) ‖d‖²`
whenever both endpoints lie in `interior (effective_domain f)`. -/
theorem block_coordinate_descent_lemma_of_slice_smooth
    (f : ((i : ι) → Ei i) → EReal)
    (block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i)
    (L : NNReal)
    (i : ι) [CompleteSpace (Ei i)]
    {x : (j : ι) → Ei j}
    (h_slice_convex :
      Convex ℝ {d : Ei i | x + 𝒰[i] d ∈ interior (effective_domain f)})
    (h_slice_smooth :
      is_l_smooth_on
        (block_coordinate_slice f x i)
        {d : Ei i | x + 𝒰[i] d ∈ interior (effective_domain f)}
        L)
    (h_block_gradient_spec :
      HasGradientAt (block_coordinate_slice f x i) (block_gradient i x) 0)
    {d : Ei i}
    (hx : x ∈ interior (effective_domain f))
    (hxd : x + 𝒰[i] d ∈ interior (effective_domain f)) :
    (f (x + 𝒰[i] d)).toReal ≤
      (f x).toReal + inner ℝ (block_gradient i x) d + ((L : ℝ) / 2) * ‖d‖ ^ (2 : ℕ) := by
  have h0 :
      (0 : Ei i) ∈ {d : Ei i | x + 𝒰[i] d ∈ interior (effective_domain f)} := by
    simpa [block_coordinate_update] using hx
  have hdescent :=
    is_l_smooth_on_descent_lemma h_slice_convex h_slice_smooth h0 hxd
  simpa
      [block_coordinate_slice_apply, block_coordinate_update, h_block_gradient_spec.gradient] using
    hdescent

namespace IsBlockProximalGradientProblem

variable [Fintype ι]
variable {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
variable {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
variable {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}
variable {Li : (i : ι) → PosReal}

omit [∀ i, InnerProductSpace ℝ (Ei i)] [Fintype ι] in
private theorem block_coordinate_update_update_sub
    (x : (j : ι) → Ei j) (i : ι) (d e : Ei i) :
    block_coordinate_update (block_coordinate_update x i d) i (e - d) =
      block_coordinate_update x i e := by
  ext j
  by_cases hji : j = i
  · subst hji
    simp [block_coordinate_update, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  · simp [block_coordinate_update, hji]

omit [∀ i, InnerProductSpace ℝ (Ei i)] [Fintype ι] in
private theorem block_coordinate_update_update
    (x : (j : ι) → Ei j) (i : ι) (d e : Ei i) :
    block_coordinate_update (block_coordinate_update x i d) i e =
      block_coordinate_update x i (d + e) := by
  ext j
  by_cases hji : j = i
  · subst j
    simp [block_coordinate_update, add_left_comm, add_comm]
  · simp [block_coordinate_update, hji]

/-- Re-centering the one-block slice at `d` identifies its gradient with the Chapter 11 block
gradient at the updated point `x + 𝒰[i] d`. -/
theorem block_coordinate_slice_hasGradientAt
    (hproblem : IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li)
    (i : ι) [CompleteSpace (Ei i)] {x : (j : ι) → Ei j} {d : Ei i}
    (hxd : x + 𝒰[i] d ∈ interior (effective_domain f)) :
    HasGradientAt
      (block_coordinate_slice f x i)
      (block_gradient i (x + 𝒰[i] d))
      d := by
  let y := block_coordinate_update x i d
  have hy :
      block_coordinate_slice f y i =
        fun e : Ei i ↦ block_coordinate_slice f x i (d + e) := by
    funext e
    simp [y, block_coordinate_slice_apply, block_coordinate_update_update]
  have hshift :
      HasGradientAt
        (fun e : Ei i ↦ block_coordinate_slice f x i (d + e))
        (block_gradient i y)
        0 := by
    have hbase :
        HasGradientAt
          (block_coordinate_slice f y i)
          (block_gradient i y)
          0 :=
      hproblem.block_partial_gradient_hasGradientAt i hxd
    rw [hy] at hbase
    exact hbase
  rw [hasGradientAt_iff_hasFDerivAt] at hshift ⊢
  simpa using (hasFDerivAt_comp_add_left d).1 hshift

/-- The Chapter 11 block-Lipschitz owner implies that the frozen one-block slice is
`L_i`-smooth on its natural admissible domain. -/
theorem block_coordinate_slice_is_l_smooth_on
    (hproblem : IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li)
    (i : ι) [CompleteSpace (Ei i)] {x : (j : ι) → Ei j} :
    is_l_smooth_on
      (block_coordinate_slice f x i)
      {d : Ei i | x + 𝒰[i] d ∈ interior (effective_domain f)}
      (PosReal.toNNReal (Li i)) := by
  rw [is_l_smooth_on_iff_forall_norm_sub_le]
  refine ⟨?_, ?_⟩
  · intro d hd
    exact (hproblem.block_coordinate_slice_hasGradientAt i hd).differentiableAt
  · intro d hd e he
    have hde :
        block_coordinate_update (block_coordinate_update x i d) i (e - d) =
          block_coordinate_update x i e :=
      block_coordinate_update_update_sub x i d e
    have hde' :
        block_coordinate_update (x + 𝒰[i] d) i (e - d) = x + 𝒰[i] e := by
      simpa [block_coordinate_update] using hde
    have he' :
        block_coordinate_update (block_coordinate_update x i d) i (e - d) ∈
          interior (effective_domain f) := by
      rw [hde]
      exact he
    have he'' :
        block_coordinate_update (x + 𝒰[i] d) i (e - d) ∈
          interior (effective_domain f) := by
      simpa [block_coordinate_update] using he'
    have hlip :=
      hproblem.block_partial_gradient_lipschitz
        i
        hd
        he''
    have hdgrad :
        HasGradientAt
          (block_coordinate_slice f x i)
          (block_gradient i (x + 𝒰[i] d))
          d :=
      hproblem.block_coordinate_slice_hasGradientAt i hd
    have hegrad :
        HasGradientAt
          (block_coordinate_slice f x i)
          (block_gradient i (x + 𝒰[i] e))
          e :=
      hproblem.block_coordinate_slice_hasGradientAt i he
    have hlip' :
        ‖block_gradient i (x + 𝒰[i] d) - block_gradient i (x + 𝒰[i] e)‖ ≤
          ↑(Li i) * ‖d - e‖ := by
      simpa [hde', norm_sub_rev] using hlip
    simpa [hdgrad.gradient, hegrad.gradient] using hlip'

end IsBlockProximalGradientProblem

namespace BlockProximalGradientAssumptions

variable [Fintype ι]
variable {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
variable {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
variable {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}
variable {Lf : NNReal} {Li : (i : ι) → PosReal}

omit [Fintype ι] in
private theorem block_coordinate_update_combo
    (x : (j : ι) → Ei j) (i : ι) (d e : Ei i) {a b : ℝ} (hab : a + b = 1) :
    a • block_coordinate_update x i d + b • block_coordinate_update x i e =
      block_coordinate_update x i (a • d + b • e) := by
  classical
  ext j
  by_cases hji : j = i
  · subst j
    calc
      a • block_coordinate_update x i d i + b • block_coordinate_update x i e i
          = (a • x i + b • x i) + (a • d + b • e) := by
              simp [block_coordinate_update, smul_add, add_assoc, add_left_comm, add_comm]
      _ = (a + b) • x i + (a • d + b • e) := by rw [← add_smul]
      _ = x i + (a • d + b • e) := by simp [hab]
      _ = block_coordinate_update x i (a • d + b • e) i := by
            simp [block_coordinate_update]
  · calc
      a • block_coordinate_update x i d j + b • block_coordinate_update x i e j
          = a • x j + b • x j := by simp [block_coordinate_update, hji]
      _ = (a + b) • x j := by rw [← add_smul]
      _ = block_coordinate_update x i (a • d + b • e) j := by
            simp [block_coordinate_update, hji, hab]

/-- The admissible one-block slice domain is convex under the Chapter 11 standing assumptions. -/
theorem block_coordinate_slice_domain_convex
    (hproblem : BlockProximalGradientAssumptions f g block_gradient XStar FOpt Lf Li)
    (i : ι) {x : (j : ι) → Ei j} :
    Convex ℝ {d : Ei i | x + 𝒰[i] d ∈ interior (effective_domain f)} := by
  let hinterior : Convex ℝ (interior (effective_domain f)) :=
    hproblem.f_effective_domain_convex.interior
  intro d hd e he a b ha hb hab
  have hcomb := hinterior hd he ha hb hab
  have hcomb' :
      a • block_coordinate_update x i d + b • block_coordinate_update x i e ∈
        interior (effective_domain f) := by
    simpa [block_coordinate_update] using hcomb
  have hcomb'' :
      block_coordinate_update x i (a • d + b • e) ∈ interior (effective_domain f) := by
    simpa [block_coordinate_update_combo x i d e hab] using hcomb'
  simpa [block_coordinate_update] using hcomb''

/-- Lemma 11.2: under Definition 11.4, the textbook one-block update satisfies the quadratic
upper model with the corresponding block Lipschitz constant `L_i`. -/
theorem block_coordinate_descent_lemma
    (hproblem : BlockProximalGradientAssumptions f g block_gradient XStar FOpt Lf Li)
    (i : ι) [CompleteSpace (Ei i)] {x : (j : ι) → Ei j} {d : Ei i}
    (hx : x ∈ interior (effective_domain f))
    (hxd : x + 𝒰[i] d ∈ interior (effective_domain f)) :
    (f (x + 𝒰[i] d)).toReal ≤
      (f x).toReal + inner ℝ (block_gradient i x) d + ((Li i : ℝ) / 2) * ‖d‖ ^ (2 : ℕ) := by
  let hcore : IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li :=
    hproblem.toIsBlockProximalGradientProblem
  have hsmooth :
      is_l_smooth_on
        (block_coordinate_slice f x i)
        {d : Ei i | x + 𝒰[i] d ∈ interior (effective_domain f)}
        (PosReal.toNNReal (Li i)) :=
    hcore.block_coordinate_slice_is_l_smooth_on i
  have hgrad : HasGradientAt (block_coordinate_slice f x i) (block_gradient i x) 0 :=
    hcore.block_partial_gradient_hasGradientAt i hx
  exact
    block_coordinate_descent_lemma_of_slice_smooth
      f
      block_gradient
      (PosReal.toNNReal (Li i))
      i
      (hproblem.block_coordinate_slice_domain_convex i)
      hsmooth
      hgrad
      hx
      hxd

end BlockProximalGradientAssumptions

end

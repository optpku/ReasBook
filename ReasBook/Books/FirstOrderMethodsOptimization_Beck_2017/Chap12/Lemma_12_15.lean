/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Algorithm_12_14
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Algorithm_12_15
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Lemma_12_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators Gradient

universe u

section

variable {E : Type u}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {p : ℕ}

variable (f : E → EReal) (g : Fin p → E → EReal) (σ : PosReal)
variable (hf_proper : IsProperExtendedRealFunction f) (hf_closed : LowerSemicontinuous f)
variable (hf_strong : StrongConvexOn (effective_domain f) (σ : ℝ) (fun x ↦ (f x).toReal))
variable (hg_proper : ∀ j : Fin p, IsProperExtendedRealFunction (g j))
variable (hg_closed : ∀ j : Fin p, LowerSemicontinuous (g j))
variable (hg_convex : ∀ j : Fin p, is_convex_function (g j))

include hf_proper hf_closed hf_strong hg_proper hg_closed hg_convex

recall dual_block_proximal_gradient_dual_step
recall dual_block_proximal_gradient_primal_y_step
recall dual_based_proximal_gradient_dual_step_iff_mem_dual_proximal_gradient_primal_y_step

/- Lemma 12.15 is `source-facing`: it identifies the Chapter 12 block dual-step owner from
Algorithm 12.14 with the Chapter 12 block primal-step owner from Algorithm 12.15 at the canonical
block stepsize `σ⁻¹`.

Domain sampling in the local convex/proximal API gives the owner chain:
- `dual_block_proximal_gradient_dual_step` as the source-facing one-block update set in dual
  coordinates;
- `dual_block_proximal_gradient_primal_y_step` as the source-facing one-block update set in primal
  coordinates; and
- Lemma 12.5 as the lower-level bridge on the active block before transporting through
  `block_coordinate_update`.

Primitive data: the strongly convex `f`, the block family `g`, the block index `i`, and the block
vector `v`.
Derived API: the explicit affine-image `prox` formula, which stays a thin companion obtained by
unfolding the primal block-step owner. -/

-- Proof sketch: specialize Lemma 12.5 to the active block `i`, the identity map, the affine
-- shift `shift = ∑ j, v j - v i`, and the canonical parameter `L = σ⁻¹`; then transport the
-- resulting equivalence through the common one-block update owner `block_coordinate_update`.
/-- Lemma 12.15: for the dual block proximal-gradient method, the Chapter 12 block dual update at
block `i` is equivalent to the Chapter 12 block primal update at the canonical point
`xTilde = ∇ f^*(∑ j, v_j)`. -/
theorem dual_block_proximal_gradient_dual_step_iff_mem_dual_block_proximal_gradient_primal_y_step
    (i : Fin p) (yNext v : Fin p → E) :
    yNext ∈ dual_block_proximal_gradient_dual_step
        (fun j z ↦ ((g j)∗) (-z))
        (∇ fun z : E ↦ (((f∗) z).toReal))
        σ
        i
        v ↔
      yNext ∈ dual_block_proximal_gradient_primal_y_step
        g
        σ
        ((∇ fun z : E ↦ (((f∗) z).toReal)) (∑ j : Fin p, v j))
        v
        i := by
  let fStarReal : E → ℝ := fun z ↦ (((f∗) z).toReal)
  let gradFStar : E → E := ∇ fStarReal
  let shift : E := ∑ j : Fin p, v j - v i
  let xTilde : E := gradFStar (∑ j : Fin p, v j)
  -- Normalize the active-block affine shift so the shifted one-block problem is centered at
  -- the total dual sum `∑ j, v j`.
  have hshift : v i + shift = ∑ j : Fin p, v j := by
    simp [shift, sub_eq_add_neg]
  -- The Fréchet derivative of the shifted conjugate pulls back to the derivative at the
  -- canonical total sum.
  have hderiv :
      fderiv ℝ (fun z : E ↦ fStarReal (z + shift)) (v i) =
        fderiv ℝ fStarReal (∑ j : Fin p, v j) := by
    rw [fderiv_comp_add_right shift]
    simp [hshift]
  -- Convert the derivative identity into the gradient value used by the Chapter 12 block API.
  have hgrad :
      ∇ (fun z : E ↦ fStarReal (z + shift)) (v i) =
        gradFStar (∑ j : Fin p, v j) := by
    simpa [fStarReal, gradFStar, gradient] using
      congrArg ((InnerProductSpace.toDual ℝ E).symm) hderiv
  have hstep :
      ∀ yiNext : E,
        yiNext ∈ dual_based_proximal_gradient_dual_step
            (fun z : E ↦ ((g i)∗) (-z))
            (fun _ : E ↦ gradFStar (∑ j : Fin p, v j))
            σ⁻¹
            (v i) ↔
          yiNext ∈ dual_proximal_gradient_primal_y_step (g i) (LinearMap.id) xTilde (v i) σ⁻¹ := by
    intro yiNext
    -- Route correction: rewrite the active-block dual owner through its membership theorem
    -- before applying Lemma 12.5, instead of asking `simpa` to normalize the owner itself.
    have hdual :
        yiNext ∈ dual_based_proximal_gradient_dual_step
            (fun z : E ↦ ((g i)∗) (-z))
            (fun _ : E ↦ gradFStar (∑ j : Fin p, v j))
            σ⁻¹
            (v i) ↔
          yiNext ∈ dual_based_proximal_gradient_dual_step
            (fun z : E ↦ ((g i)∗) (-z))
            (fun z : E ↦ ∇ (fun w : E ↦ fStarReal (w + shift)) z)
            σ⁻¹
            (v i) := by
      rw [mem_dual_based_proximal_gradient_dual_step_iff,
        mem_dual_based_proximal_gradient_dual_step_iff,
        hgrad]
    -- Specialize Lemma 12.5 on the active block and transport it through the normalized owner.
    exact hdual.trans <| by
      simpa [xTilde, gradFStar, fStarReal, hshift] using
        (dual_based_proximal_gradient_dual_step_iff_mem_dual_proximal_gradient_primal_y_step
          σ f (g i) (LinearMap.id) shift hf_proper hf_closed hf_strong
          (hg_proper i) (hg_closed i) (hg_convex i) yiNext (v i) σ⁻¹)
  change yNext ∈ (fun yiNext ↦ block_coordinate_update v i (yiNext - v i)) ''
      dual_based_proximal_gradient_dual_step
        (fun z : E ↦ ((g i)∗) (-z))
        (fun _ : E ↦ gradFStar (∑ j : Fin p, v j))
        σ⁻¹
        (v i) ↔
    yNext ∈ (fun yiNext ↦ block_coordinate_update v i (yiNext - v i)) ''
      dual_proximal_gradient_primal_y_step
        (g i)
        (LinearMap.id)
        xTilde
        (v i)
        σ⁻¹
  constructor
  · rintro ⟨yiNext, hyiNext, rfl⟩
    exact ⟨yiNext, (hstep yiNext).mp hyiNext, rfl⟩
  · rintro ⟨yiNext, hyiNext, rfl⟩
    exact ⟨yiNext, (hstep yiNext).mpr hyiNext, rfl⟩

-- Proof sketch: unfold `dual_block_proximal_gradient_primal_y_step` and then expand the active
-- one-block owner `dual_proximal_gradient_primal_y_step` at the canonical value `L = σ⁻¹`.
/-- Lemma 12.15, explicit affine-image form: the same block-owner equivalence as above, with the
right-hand side written as the updated-block image of the textbook affine correction of
`prox_{g_i / σ}(xTilde - y_i / σ)`. -/
theorem dual_block_proximal_gradient_dual_step_iff_mem_update_image_scaled_prox
    (i : Fin p) (yNext v : Fin p → E) :
    yNext ∈ dual_block_proximal_gradient_dual_step
        (fun j z ↦ ((g j)∗) (-z))
        (∇ fun z : E ↦ (((f∗) z).toReal))
        σ
        i
        v ↔
      yNext ∈ (fun yiNext ↦ block_coordinate_update v i (yiNext - v i)) ''
        ((fun z : E ↦
            v i - (σ : ℝ) • ((∇ fun x : E ↦ (((f∗) x).toReal)) (∑ j : Fin p, v j)) +
              (σ : ℝ) • z) ''
          prox[(((σ⁻¹ : PosReal) : EReal) • (g i))]
            (((∇ fun x : E ↦ (((f∗) x).toReal)) (∑ j : Fin p, v j)) - (σ⁻¹ : ℝ) • v i)) := by
  have hσ0 : (σ : ℝ) ≠ 0 := ne_of_gt σ.2
  have hσ : (1 / (σ⁻¹ : PosReal) : ℝ) = (σ : ℝ) := by
    change (1 : ℝ) / ((σ : ℝ)⁻¹) = (σ : ℝ)
    field_simp [hσ0]
  have hupdate :
      (fun yiNext : E ↦ block_coordinate_update v i (yiNext - v i)) = Function.update v i := by
    funext yiNext
    simpa [sub_eq_add_neg] using
      (block_coordinate_update_eq_update v i (yiNext - v i))
  simpa [dual_block_proximal_gradient_primal_y_step, dual_proximal_gradient_primal_y_step, hσ,
    hupdate] using
    dual_block_proximal_gradient_dual_step_iff_mem_dual_block_proximal_gradient_primal_y_step
      f g σ hf_proper hf_closed hf_strong hg_proper hg_closed hg_convex i yNext v

omit hf_proper hf_closed hf_strong hg_proper hg_closed hg_convex

end

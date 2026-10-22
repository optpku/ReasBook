/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Proposition_6_2_1
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_30

-- Declarations for this item will be appended below by the statement pipeline.

/-
Definition 11.7 is a `bridge/view` in the Chapter 11 block proximal-gradient domain.

Domain sampling identifies the relevant declarations as follows:
- `block_partial_gradient_mapping` from Definition 11.4 is the Chapter 11 `source-facing` owner
  for the one-block residual `G_L^i(x)`;
- the notation `(G[L; g, block_gradient, hg_proper, hg_closed, hg_convex]) x i` is the canonical
  theorem-surface spelling of that owner;
- `block_partial_gradient_mapping_def` is the defining residual formula;
- Theorem 10.7's zero-penalty specialization is the nearby canonical pattern for collapsing a
  prox-gradient residual to an ordinary gradient when the penalty vanishes.

The primitive data are only the block penalties `g_i`, the chosen block gradient map, the
positive stepsize `L`, the base point `x`, and the block index `i`. Since the upstream Chapter 11
owner file is not part of the local proof frontier for this item, this file keeps a private
file-local owner for the one-block residual and proves only the interior-domain bridge statement
for Definition 11.7. -/

noncomputable section

universe u v

open scoped Gradient

section

variable {ι : Type u} {Ei : ι → Type v}
variable [∀ i, NormedAddCommGroup (Ei i)] [∀ i, InnerProductSpace ℝ (Ei i)]
variable [∀ i, ProperSpace (Ei i)]
variable (f : ((i : ι) → Ei i) → EReal) (g : (i : ι) → Ei i → EReal)
variable (block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i)
variable (hg_proper : ∀ i, IsProperExtendedRealFunction (g i))
variable (hg_closed : ∀ i, LowerSemicontinuous (g i))
variable (hg_convex : ∀ i, is_convex_function (g i))

set_option quotPrecheck false in
local notation "BlockSpace" => ((j : ι) → Ei j)

/-- Helper for Definition 11.7: the one-block proximal-gradient point is the unique proximal point
of the scaled block penalty at the translated block-gradient step. -/
private def block_partial_prox_grad_point_local
    (L : PosReal) (i : ι) (x : BlockSpace) : Ei i :=
  let hscaled := scaled_function_proper_closed_convex_of_pos
    (g i) (hg_proper i) (hg_closed i) (hg_convex i) (1 / L)
  Classical.choose <|
    prox_eq_singleton_of_proper_closed_convex
      ((((1 / L : PosReal) : EReal) • g i))
      hscaled.1
      hscaled.2.1
      hscaled.2.2
      (x i - (1 / L : ℝ) • block_gradient i x)

/-- Helper for Definition 11.7: the one-block partial gradient mapping is the stepsize-scaled
residual of the ambient block point and its one-block proximal-gradient update. -/
private def block_partial_gradient_mapping_local
    (L : PosReal) (i : ι) (x : BlockSpace) : Ei i :=
  (L : ℝ) • (x i - block_partial_prox_grad_point_local g block_gradient hg_proper hg_closed
    hg_convex L i x)

set_option quotPrecheck false in
local notation3:max
    "T[" L "; " g ", " block_gradient ", " hg_proper ", " hg_closed ", " hg_convex "]" =>
  fun x i ↦
    block_partial_prox_grad_point_local g block_gradient hg_proper hg_closed hg_convex L i x

set_option quotPrecheck false in
local notation3:max
    "T[" L "; " g ", " block_gradient ", " hg_proper ", " hg_closed ", " hg_convex "]" x:arg
      i:arg =>
  block_partial_prox_grad_point_local g block_gradient hg_proper hg_closed hg_convex L i x

set_option quotPrecheck false in
local notation3:max
    "G[" L "; " g ", " block_gradient ", " hg_proper ", " hg_closed ", " hg_convex "]" =>
  fun x i ↦
    block_partial_gradient_mapping_local g block_gradient hg_proper hg_closed hg_convex L i x

set_option quotPrecheck false in
local notation3:max
    "G[" L "; " g ", " block_gradient ", " hg_proper ", " hg_closed ", " hg_convex "]" x:arg
      i:arg =>
  block_partial_gradient_mapping_local g block_gradient hg_proper hg_closed hg_convex L i x

/-- The one-block prox-gradient point is the unique proximal point of `(1 / L) g_i` at
`x_i - (1 / L) • block_gradient i x`. -/
theorem block_partial_prox_grad_point_eq_singleton_on_interior
    (L : PosReal) (i : ι) (x : BlockSpace) :
    prox[((((1 / L : PosReal) : EReal) • g i))]
      (x i - (1 / L : ℝ) • block_gradient i x) =
      {(T[L; g, block_gradient, hg_proper, hg_closed, hg_convex]) x i} := by
  let hscaled :=
    scaled_function_proper_closed_convex_of_pos
      (g i) (hg_proper i) (hg_closed i) (hg_convex i) (1 / L)
  -- The Chapter 11 owner `T_L^i` is defined by choosing the unique element of the corresponding
  -- scaled proximal singleton.
  simpa [block_partial_prox_grad_point_local, hscaled] using
    (Classical.choose_spec <|
      prox_eq_singleton_of_proper_closed_convex
        ((((1 / L : PosReal) : EReal) • g i))
        hscaled.1
        hscaled.2.1
        hscaled.2.2
        (x i - (1 / L : ℝ) • block_gradient i x))

/-- Evaluating the Chapter 11 owner `G_L^i` at an interior-domain point gives the residual
`L • (x_i - T_L^i(x))`. -/
@[simp] theorem partial_gradient_mapping_apply
    (L : PosReal) (i : ι) (x : BlockSpace) :
    (G[L; g, block_gradient, hg_proper, hg_closed, hg_convex]) x i =
      (L : ℝ) •
        (x i -
          (T[L; g, block_gradient, hg_proper, hg_closed, hg_convex]) x i) := by
  rfl

/-- Helper for Definition 11.7: when the `i`th block penalty is the zero function, the scaled
proximal mapping for that block is the singleton containing the translated gradient step. -/
theorem scaled_zero_block_penalty_prox_eq_singleton
    (L : PosReal) (i : ι) (hgi_zero : g i = 0) (x : BlockSpace) :
    prox[((((1 / L : PosReal) : EReal) • g i))]
      (x i - (1 / L : ℝ) • block_gradient i x) =
      {x i - (1 / L : ℝ) • block_gradient i x} := by
  let _ := (inferInstance : ∀ j, ProperSpace (Ei j))
  -- Rewrite the block penalty to the zero function and use the Chapter 6 zero-objective prox
  -- computation at the translated block point.
  rw [hgi_zero]
  simpa using
    (prox_zero_eq_singleton
      (x i - (1 / L : ℝ) • block_gradient i x))

/-- Helper for Definition 11.7: if the `i`th block penalty vanishes, then the Chapter 11
one-block proximal-gradient point is the translated block gradient step. -/
theorem block_partial_prox_grad_point_eq_gradient_step_of_block_penalty_eq_zero
    (L : PosReal) (i : ι) (hgi_zero : g i = 0) (x : BlockSpace) :
    (T[L; g, block_gradient, hg_proper, hg_closed, hg_convex]) x i =
      x i - (1 / L : ℝ) • block_gradient i x := by
  -- Compare the two singleton descriptions of the same proximal set: the Chapter 11 singleton
  -- owner identifies it with `{T_L^i(x)}`, while the zero-penalty specialization identifies it
  -- with the translated gradient step.
  apply Set.singleton_injective
  calc
    {(T[L; g, block_gradient, hg_proper, hg_closed, hg_convex]) x i} =
        prox[((((1 / L : PosReal) : EReal) • g i))]
          (x i - (1 / L : ℝ) • block_gradient i x) := by
      symm
      exact block_partial_prox_grad_point_eq_singleton_on_interior
        g block_gradient hg_proper hg_closed hg_convex L i x
    _ = {x i - (1 / L : ℝ) • block_gradient i x} := by
      exact scaled_zero_block_penalty_prox_eq_singleton
        g block_gradient L i hgi_zero x

/-- Helper for Definition 11.7: the Chapter 11 one-block residual `G_L^i(x)` collapses to the
chosen block gradient when the `i`th block penalty is zero. -/
theorem partial_gradient_mapping_apply_eq_block_gradient_of_block_penalty_eq_zero
    (L : PosReal) (i : ι) (hgi_zero : g i = 0) (x : BlockSpace) :
    (G[L; g, block_gradient, hg_proper, hg_closed, hg_convex]) x i =
      block_gradient i x := by
  have hT :
      (T[L; g, block_gradient, hg_proper, hg_closed, hg_convex]) x i =
        x i - (1 / L : ℝ) • block_gradient i x := by
    exact block_partial_prox_grad_point_eq_gradient_step_of_block_penalty_eq_zero
      g block_gradient hg_proper hg_closed hg_convex L i hgi_zero x
  have hL : ((L : ℝ) * (1 / L : ℝ)) = 1 := by
    field_simp [show (L : ℝ) ≠ 0 by exact (PosReal.coe_pos L).ne']
  -- Rewrite the residual by the explicit prox point from the previous helper, then collapse the
  -- scalar factor `L • ((1 / L) • ·)` to the identity.
  calc
    (G[L; g, block_gradient, hg_proper, hg_closed, hg_convex]) x i =
        (L : ℝ) •
          (x i -
            (T[L; g, block_gradient, hg_proper, hg_closed, hg_convex]) x i) := by
      rw [partial_gradient_mapping_apply]
    _ = (L : ℝ) • ((1 / L : ℝ) • block_gradient i x) := by
      rw [hT]
      simp
    _ = block_gradient i x := by
      rw [smul_smul, hL, one_smul]

-- Proof sketch: extensionality on `interior (effective_domain f)` reduces the statement to the
-- proximal characterization of `T_L^i`; when `g i = 0`, the proximal point is the translated
-- point itself, so the residual collapses to `block_gradient i x`.
/-- Definition 11.7: if the `i`th block penalty vanishes identically, then the `i`th partial
gradient mapping
namely `x ↦ (G[L; g, block_gradient, hg_proper, hg_closed, hg_convex]) x i`, coincides on
`interior (effective_domain f)` with the map `x ↦ block_gradient i x`, which encodes
`x ↦ ∇_i f(x)` in the standing block setup. -/
theorem partial_gradient_mapping_eq_block_gradient_of_block_penalty_eq_zero
    (L : PosReal) (i : ι) (hgi_zero : g i = 0) :
    (fun x : interior (effective_domain f) ↦
      (G[L; g, block_gradient, hg_proper, hg_closed, hg_convex]) (x : BlockSpace) i) =
      fun x : interior (effective_domain f) ↦ block_gradient i (x : BlockSpace) := by
  -- Function extensionality reduces the statement to the pointwise residual collapse proved
  -- above.
  funext x
  simpa using partial_gradient_mapping_apply_eq_block_gradient_of_block_penalty_eq_zero
    g block_gradient hg_proper hg_closed hg_convex L i hgi_zero (x : BlockSpace)

end

/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_1
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_6
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_7
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Definition_13_16
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Definition_13_17

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe v

open scoped Gradient

section

variable {ι : Type v} [Fintype ι] {Ei : ι → Type v}
variable [∀ i, NormedAddCommGroup (Ei i)]
variable [∀ i, InnerProductSpace ℝ (Ei i)]

local notation "X" => PiLp 2 Ei

/- `prompt_add/` is absent in this workspace, so the statement design is sampled directly from the
nearby Chapter 13 block conditional-gradient owners. This item is `source-facing`: it records the
realized RGBCG update rule along one sample path, using only the sampled block index `i_k` and the
corresponding chosen minimizer of that block subproblem at step `k`.

Domain sampling against the local API identifies the relevant canonical owners:
- Chapter 11's source-facing block insertion notation `𝒰[i]` for the realized one-block update
  `x^k + 𝒰[i_k] (d_k)`, implemented by `PiLp.single 2 i_k`, with
  `d_k = t_k • (p^k - x^k_{i_k})`;
- `partial_conditional_gradient_argmin` from Definition 13.17 for the primitive admissible set of
  block minimizers at the sampled block `i_k`;
- `effective_domain (PiLp.separableSum g)` for the initialization clause
  `x⁰ ∈ dom(g)`.

As in Algorithm 13.2, the public owner is a pathwise trajectory predicate on explicit iterate and
chosen-minimizer data. Probability-law assumptions such as measurability, independence, or
uniformity of the sampled blocks belong to the downstream stochastic layer, not to this owner. The
one-step map itself is written on the theorem surface using the canonical Chapter 11 notation
`𝒰[i]`. -/

/-- Algorithm 13.7: for an initial point `x⁰ ∈ dom(g)`, a realized sequence `sampled_block k = i_k`
of sampled block indices, sampled-block minimizers `p^k ∈ argmin_v {⟪v, ∇_{i_k} f(x^k)⟫ +
g_{i_k}(v)}`, and stepsizes `t_k ∈ [0, 1]`, the iterates `x^k` follow the randomized generalized
block conditional gradient method when
`x^{k+1} = x^k + 𝒰[i_k] (t_k • (p^k - x^k_{i_k}))`. As in Algorithm 13.2, the primitive trajectory
data are exactly the initialization clause, the sampled-block argmin clause, and the one-block
update equality; the accessor lemmas below are derived API. -/
class is_randomized_generalized_block_conditional_gradient_trajectory
    (g : (i : ι) → Ei i → EReal)
    (block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i)
    (x : ℕ → X) (sampled_block : ℕ → ι)
    (point : (k : ℕ) → Ei (sampled_block k))
    (t : ℕ → Set.Icc (0 : ℝ) 1) : Prop where
  /-- The initial iterate lies in `dom(g)`. -/
  zero_mem_effective_domain : x 0 ∈ effective_domain (PiLp.separableSum g)
  /-- At each iteration, the sampled-block point solves the sampled linearized subproblem. -/
  argmin_mem (k : ℕ) :
    point k ∈ partial_conditional_gradient_argmin g block_gradient (x k) (sampled_block k)
  /-- At each iteration, the update changes only the realized sampled block. -/
  step_eq (k : ℕ) :
    x (k + 1) =
      x k + 𝒰[sampled_block k] ((t k : ℝ) • (point k - x k (sampled_block k)))

-- Proof sketch: extract the initialization clause from the first conjunct of
-- `is_randomized_generalized_block_conditional_gradient_trajectory`.
/-- A RGBCG trajectory starts from a point of `dom(g)`. -/
theorem is_randomized_generalized_block_conditional_gradient_trajectory_zero
    {g : (i : ι) → Ei i → EReal}
    {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
    {x : ℕ → X} {sampled_block : ℕ → ι}
    {point : (k : ℕ) → Ei (sampled_block k)} {t : ℕ → Set.Icc (0 : ℝ) 1}
    (h : is_randomized_generalized_block_conditional_gradient_trajectory
      g block_gradient x sampled_block point t) :
    x 0 ∈ effective_domain (PiLp.separableSum g) :=
  h.zero_mem_effective_domain

-- Proof sketch: specialize the defining universal clause of
-- `is_randomized_generalized_block_conditional_gradient_trajectory` at the iteration index `k` and
-- project its first component.
/-- At iteration `k`, a RGBCG trajectory uses a sampled-block minimizer `p^k` of the linearized
subproblem for the realized block `i_k`. -/
theorem is_randomized_generalized_block_conditional_gradient_trajectory_argmin
    {g : (i : ι) → Ei i → EReal}
    {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
    {x : ℕ → X} {sampled_block : ℕ → ι}
    {point : (k : ℕ) → Ei (sampled_block k)} {t : ℕ → Set.Icc (0 : ℝ) 1}
    (h : is_randomized_generalized_block_conditional_gradient_trajectory
      g block_gradient x sampled_block point t)
    (k : ℕ) :
    point k ∈ partial_conditional_gradient_argmin g block_gradient (x k) (sampled_block k) :=
  h.argmin_mem k

-- Proof sketch: specialize the defining recursive-update clause of
-- `is_randomized_generalized_block_conditional_gradient_trajectory` at the iteration index `k`.
/-- At each iteration `k`, a RGBCG trajectory updates by the realized sampled-block rule
`x^{k+1} = x^k + 𝒰[i_k] (t_k • (p^k - x^k_{i_k}))`. -/
theorem is_randomized_generalized_block_conditional_gradient_trajectory_step
    {g : (i : ι) → Ei i → EReal}
    {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
    {x : ℕ → X} {sampled_block : ℕ → ι}
    {point : (k : ℕ) → Ei (sampled_block k)} {t : ℕ → Set.Icc (0 : ℝ) 1}
    (h : is_randomized_generalized_block_conditional_gradient_trajectory
      g block_gradient x sampled_block point t)
    (k : ℕ) :
    x (k + 1) =
      x k + 𝒰[sampled_block k] ((t k : ℝ) • (point k - x k (sampled_block k))) :=
  h.step_eq k

end

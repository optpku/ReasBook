/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap11.Definition_11_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open scoped Gradient

section

variable {ι : Type u} {Ei : ι → Type v}
variable [Fintype ι]
variable [∀ i, NormedAddCommGroup (Ei i)] [∀ i, InnerProductSpace ℝ (Ei i)]
variable [∀ i, ProperSpace (Ei i)]
variable {Li : (i : ι) → PosReal}

variable {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
variable {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
variable {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}

/- Algorithm 11.5 is `source-facing`: the chapter introduces the randomized block proximal
gradient iteration obtained by following a realized block sequence `k ↦ i_k` and performing the
corresponding one-block prox-gradient update. The probability law itself is not a new owner-level
object here; the reusable mathematical owner is the pathwise iterate sequence attached to that
realized sample path, built directly from the existing Chapter 11 block-problem owner
`IsBlockProximalGradientProblem` together with `block_coordinate_update` and `T[...]`.

Primitive data are only the actual starting point and the realized sampled blocks. The textbook
admissibility condition `x^0 ∈ int(dom f)` is theorem-level data used later to prove well-defined
domain properties of the iterates, not data used by the recursion itself, so it should not remain
bundled into the owner definition. The uniform sampling law belongs to the downstream
probabilistic layer. -/

/-- Algorithm 11.5, as a pathwise recursion: from an initial point `x0` and a realized sequence
`sampled_block k = i_k` of block indices, the randomized block proximal-gradient iterates satisfy
`x^0 = x0` and
`x^{k+1} = block_coordinate_update x^k i_k (T_{L_{i_k}}^{i_k}(x^k) - x^k_{i_k})`.

Later Chapter 11 results apply this owner to initial data known to lie in `int(dom f)`, but that
admissibility is not primitive data of the recursion itself. -/
def randomized_block_proximal_gradient_method
    (hproblem : IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li)
    (x0 : (i : ι) → Ei i) (sampled_block : ℕ → ι) :
    ℕ → ((i : ι) → Ei i)
  | 0 => x0
  | k + 1 =>
      let xk :=
        randomized_block_proximal_gradient_method hproblem x0 sampled_block k
      let ik := sampled_block k
      block_coordinate_update
        xk
        ik
        (hproblem.prox_point (Li ik) ik xk - xk ik)

section

variable (hproblem : IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li)
variable (x0 : (i : ι) → Ei i)
variable (sampled_block : ℕ → ι)

-- Proof sketch: unfold the recursive definition of
-- `randomized_block_proximal_gradient_method` at `0`.
/-- The RBPG iterate sequence starts at the prescribed initial point `x^0`. -/
@[simp] theorem randomized_block_proximal_gradient_method_zero :
    randomized_block_proximal_gradient_method hproblem x0 sampled_block 0 = x0 :=
  rfl

-- Proof sketch: unfold `randomized_block_proximal_gradient_method` at `k + 1`; the recursion
-- applies one realized RBPG step to the current iterate using the sampled block `sampled_block k`.
/-- At step `k`, the next RBPG iterate is obtained by applying the realized one-block update in
the sampled block `i_k = sampled_block k`. -/
theorem randomized_block_proximal_gradient_method_succ (k : ℕ) :
    randomized_block_proximal_gradient_method hproblem x0 sampled_block (k + 1) =
      block_coordinate_update
        (randomized_block_proximal_gradient_method hproblem x0 sampled_block k)
        (sampled_block k)
        (hproblem.prox_point
            (Li (sampled_block k))
            (sampled_block k)
            (randomized_block_proximal_gradient_method hproblem x0 sampled_block k) -
          (randomized_block_proximal_gradient_method hproblem x0 sampled_block k)
            (sampled_block k)) :=
  rfl

end

end

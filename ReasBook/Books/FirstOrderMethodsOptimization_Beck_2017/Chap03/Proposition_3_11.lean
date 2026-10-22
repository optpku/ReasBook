/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_9
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_12

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Filter
open InnerProductSpace (toDual)
open scoped Topology RealInnerProductSpace Gradient

noncomputable section

section

variable {E : Type u} {ι : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [Finite ι] [Nonempty ι]

/- Proposition 3.11 is a `bridge/view` item on the chapter owner layer of finite nonempty index
types: the owner max rule is `directional_derivative_iSup_eq_iSup_active_indices`, and the owner
calculus bridges are `has_directional_derivative_at_of_mem_interior_of_hasLineDerivAt` and
`directional_derivative_eq_of_mem_interior_of_hasFDerivAt`, organized around the chapter owner
predicate `is_differentiable_at`. The active-indexed gradient pairing formula is therefore derived
from those owner declarations rather than from a second local `Fin`-specific wrapper or a
proof-artifact `effective_domain`/global-`≠ ⊥` interface. -/
recall finite_domain
recall is_differentiable_at
recall directional_derivative_iSup_eq_iSup_active_indices
recall directional_derivative_eq_of_mem_interior_of_hasFDerivAt

-- Proof sketch: unpack `is_differentiable_at (f i) x` into the owner interior-finite-domain
-- hypothesis and differentiability of `y ↦ (f i y).toReal`. The former gives the local
-- finiteness needed to construct the directional derivative of each summand, and the latter
-- identifies that derivative with the inner product of the gradient against `d`. Applying the
-- finite-family active-index max rule and substituting these values yields the formula.
/-- Proposition 3.11: if each function in a finite family of extended-real-valued functions is
differentiable at `x` in the sense of Definition 3.10, then the directional derivative of the
pointwise maximum is the maximum of the active gradient pairings `⟪∇ f_i(x), d⟫`. -/
theorem directional_derivative_pointwise_max_eq_sup'_active_gradient_pairings
    (f : ι → E → EReal) (x d : E) (hdiff : ∀ i : ι, is_differentiable_at (f i) x) :
    directional_derivative (fun y ↦ ⨆ i : ι, f i y) x d =
      iSup fun i : {i : ι // f i x = iSup fun j : ι ↦ f j x} ↦
        ((⟪∇ (fun y ↦ (f i y).toReal) x, d⟫ : ℝ) : EReal) := by
  have hxfinite : ∀ i : ι, x ∈ interior (finite_domain (f i)) := fun i ↦ (hdiff i).1
  have hderiv :
      ∀ i : ι,
        HasFDerivAt (fun y ↦ (f i y).toReal)
          (toDual ℝ E (∇ (fun y ↦ (f i y).toReal) x)) x := by
    intro i
    exact (hdiff i).2.hasGradientAt.hasFDerivAt
  have hdir : ∀ i : ι, ∃ ℓ : ℝ, has_directional_derivative_at (f i) x d (ℓ : EReal) := by
    intro i
    have hline :
        HasLineDerivAt ℝ (fun y ↦ (f i y).toReal)
          (⟪∇ (fun y ↦ (f i y).toReal) x, d⟫) x d := by
      simpa using (hderiv i).hasLineDerivAt d
    exact
      ⟨(⟪∇ (fun y ↦ (f i y).toReal) x, d⟫ : ℝ),
        has_directional_derivative_at_of_mem_interior_of_hasLineDerivAt (hxfinite i) hline⟩
  have hx : x ∈ ⋂ i : ι, interior (finite_domain (f i)) := by
    simpa [Set.mem_iInter] using hxfinite
  calc
    directional_derivative (fun y ↦ ⨆ i : ι, f i y) x d
        = iSup fun i : {i : ι // f i x = iSup fun j : ι ↦ f j x} ↦
            directional_derivative (f i) x d :=
      directional_derivative_iSup_eq_iSup_active_indices f x d hx hdir
    _ = iSup fun i : {i : ι // f i x = iSup fun j : ι ↦ f j x} ↦
          ((⟪∇ (fun y ↦ (f i y).toReal) x, d⟫ : ℝ) : EReal) := by
      congr with i
      simpa using
        directional_derivative_eq_of_mem_interior_of_hasFDerivAt
          (hxfinite i) (hderiv i) d

end

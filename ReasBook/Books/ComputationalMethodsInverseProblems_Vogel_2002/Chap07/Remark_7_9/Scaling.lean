/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Definition_2_15

public section

noncomputable section

namespace ContinuousLinearMap.SingularSystem

universe u v

variable {H₁ : Type u} {H₂ : Type v}
variable [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂] [CompleteSpace H₂]
variable {K : H₁ →L[ℝ] H₂}

/-- The source-faithful positive-index bridge for the Chapter 7 singular-value
sequence: `i = 1` is sent to the first internal singular mode. -/
@[expose]
def positiveIndex (S : SingularSystem K) (h_length : S.length = ⊤) :
    ℕ+ → S.Index :=
  fun i ↦ S.natIndex h_length i.natPred

@[simp] theorem positiveIndex_apply
    (S : SingularSystem K) (h_length : S.length = ⊤) (i : ℕ+) :
    S.positiveIndex h_length i = S.natIndex h_length i.natPred := rfl

@[simp] theorem positiveIndex_one
    (S : SingularSystem K) (h_length : S.length = ⊤) :
    S.positiveIndex h_length 1 = S.natIndex h_length 0 := by
  rw [positiveIndex_apply]
  norm_num [PNat.natPred]

@[simp] theorem positiveIndex_succPNat
    (S : SingularSystem K) (h_length : S.length = ⊤) (n : ℕ) :
    S.positiveIndex h_length n.succPNat = S.natIndex h_length n := by
  simp [positiveIndex]

/-- When the singular data of `K` are indexed by all positive integers, the
singular values form the Chapter 7 sequence `i ↦ s_i` used in `(7.49)` and
Remark 7.9, with `i = 1` corresponding to the first singular mode. -/
@[expose]
def singularValueSequence (S : SingularSystem K) (h_length : S.length = ⊤) :
    ℕ+ → ℝ :=
  fun i ↦ S.singularValue (S.positiveIndex h_length i)

@[simp] theorem singularValueSequence_apply
    (S : SingularSystem K) (h_length : S.length = ⊤) (i : ℕ+) :
    S.singularValueSequence h_length i = S.singularValue (S.natIndex h_length i.natPred) := by
  simp [singularValueSequence]

/-- The singular values of `S` satisfy the Chapter 7 algebraic square-decay law
`(7.49)`. -/
abbrev HasAlgebraicSingularValueSquareDecay
    (S : SingularSystem K) (h_length : S.length = ⊤) (c p : ℝ) : Prop :=
  ∀ i : ℕ+, S.singularValueSequence h_length i ^ 2 = c * (i : ℝ) ^ (-p)

@[simp] theorem hasAlgebraicSingularValueSquareDecay_iff
    (S : SingularSystem K) (h_length : S.length = ⊤) (c p : ℝ) :
    S.HasAlgebraicSingularValueSquareDecay h_length c p ↔
      ∀ i : ℕ+, S.singularValueSequence h_length i ^ 2 = c * (i : ℝ) ^ (-p) :=
  Iff.rfl

end ContinuousLinearMap.SingularSystem

/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.Convergence.ProofSupport.GeneratedHistory
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.Convergence.ProofSupport.CertificateDynamics

@[expose] public section

open scoped BigOperators
open ADMM.FiniteMemory

namespace ADMM.ConvergenceProof

/-- Generated subgradient data above a zero KKT pair give nonnegative tilted
values in every finite-memory window. -/
theorem generatedValues_nonneg {m ℓ : ℕ} {γ : ℝ}
    (f : Block → (Fin m → ℝ) → EReal) (η w : ℕ → Fin m → ℝ)
    (hzero : ∀ b, IsSubgradientAt (f b) 0 0)
    (hgraph : ∀ b k, IsSubgradientAt (f b) (generatedNormal γ η w b k)
      (generatedPosition η w b k)) (k : ℕ) (b : Block) (j : Fin (ℓ + 1)) :
    0 ≤ generatedValues f η w k b j :=
  tiltedValue_nonneg (hzero b) (hgraph b (k + j.rev.val))

/-- Generated support planes give the current-value bounds in each window. -/
theorem generatedValues_current {m ℓ : ℕ} {γ : ℝ}
    (f : Block → (Fin m → ℝ) → EReal) (η w : ℕ → Fin m → ℝ)
    (hzero : ∀ b, IsSubgradientAt (f b) 0 0)
    (hgraph : ∀ b k, IsSubgradientAt (f b) (generatedNormal γ η w b k)
      (generatedPosition η w b k)) (k : ℕ) (b : Block) :
    generatedValues (ℓ := ℓ) f η w k b 0 ≤ ∑ a : Fin m,
      graphNormal γ b (fun i ↦ generatedHistory (ℓ := ℓ) η w k i a) 0 *
        graphPosition b (fun i ↦ generatedHistory (ℓ := ℓ) η w k i a) 0 := by
  simpa only [generatedValues, graphNormal_coordinate, graphPosition_coordinate,
    generatedHistory_normal, generatedHistory_position, sub_zero, dotProduct] using
    tiltedValue_le_pairing (hzero b) (hgraph b (k + (0 : Fin (ℓ + 1)).rev.val))

/-- Generated directed support planes give every lag comparison in a window. -/
theorem generatedValues_support {m ℓ : ℕ} {γ : ℝ}
    (f : Block → (Fin m → ℝ) → EReal) (η w : ℕ → Fin m → ℝ)
    (hgraph : ∀ b k, IsSubgradientAt (f b) (generatedNormal γ η w b k)
      (generatedPosition η w b k)) (k : ℕ) (b : Block) (i j : Fin (ℓ + 1)) :
    generatedValues f η w k b j - generatedValues f η w k b i ≤ ∑ a : Fin m,
      graphNormal γ b (fun t ↦ generatedHistory (ℓ := ℓ) η w k t a) j *
        (graphPosition b (fun t ↦ generatedHistory (ℓ := ℓ) η w k t a) j -
          graphPosition b (fun t ↦ generatedHistory (ℓ := ℓ) η w k t a) i) := by
  simpa only [generatedValues, graphNormal_coordinate, graphPosition_coordinate,
    generatedHistory_normal, generatedHistory_position, sub_zero, dotProduct,
    Pi.sub_apply, Pi.zero_apply, sub_zero] using
    tiltedValue_support 0 0 (hgraph b (k + i.rev.val)) (hgraph b (k + j.rev.val))

/-- The directed interpolation inequalities also hold when either endpoint is
the KKT origin, completing the lower-bound side of the certificate. -/
theorem generatedValues_gap {m ℓ : ℕ} {γ : ℝ}
    (f : Block → (Fin m → ℝ) → EReal) (η w : ℕ → Fin m → ℝ)
    (hzero : ∀ b, IsSubgradientAt (f b) 0 0)
    (hgraph : ∀ b k, IsSubgradientAt (f b) (generatedNormal γ η w b k)
      (generatedPosition η w b k)) (k : ℕ) (b : Block) (i j : Option (Fin ℓ)) :
    0 ≤ predecessorValues (generatedValues f η w k) b i -
      predecessorValues (generatedValues f η w k) b j -
      ∑ a : Fin m,
        interpolationNormal γ b j (fun t ↦ generatedHistory (ℓ := ℓ) η w k (t.1.succ, t.2) a) *
          (interpolationPosition b i (fun t ↦ generatedHistory (ℓ := ℓ) η w k (t.1.succ, t.2) a) -
            interpolationPosition b j (fun t ↦ generatedHistory (ℓ := ℓ) η w k (t.1.succ, t.2) a)) := by
  have horigin : ∀ Z : (Fin (ℓ + 1) × Fin 2) → ℝ,
      interpolationPosition b none Z = 0 := fun _ ↦ rfl
  cases i with
  | none =>
    cases j with
    | none => simp [predecessorValues, interpolationNormal, interpolationPosition]
    | some j =>
      have h := tiltedValue_le_pairing (hzero b) (hgraph b (k + j.rev.val))
      simp only [sub_zero, dotProduct] at h
      simp only [predecessorValues, generatedValues, Fin.rev_succ, Fin.val_castSucc,
        generatedHistory_interpolationNormal, generatedHistory_interpolationPosition,
        horigin, zero_sub, mul_neg, Finset.sum_neg_distrib, sub_neg_eq_add]
      linarith
  | some i =>
    cases j with
    | none =>
      simpa only [predecessorValues, generatedValues, Fin.rev_succ, Fin.val_castSucc,
        interpolationNormal, zero_mul, Finset.sum_const_zero, sub_zero] using
        tiltedValue_nonneg (hzero b) (hgraph b (k + i.rev.val))
    | some j =>
      have h := tiltedValue_support 0 0 (hgraph b (k + i.rev.val))
        (hgraph b (k + j.rev.val))
      simp only [sub_zero, dotProduct, Pi.sub_apply, Pi.zero_apply, sub_zero,
        mul_sub, Finset.sum_sub_distrib] at h
      simp only [predecessorValues, generatedValues, Fin.rev_succ, Fin.val_castSucc,
        generatedHistory_interpolationNormal, generatedHistory_interpolationPosition,
        mul_sub, Finset.sum_sub_distrib]
      linarith

/-- A valid certificate applied to a generated normalized reduced orbit makes
both its nonnegative objective merit and residual coordinates summable. All
support inequalities are derived from actual subgradient relations. -/
theorem generated_certificate_summable {m ℓ : ℕ} {γ : ℝ}
    (c : Certificate ℓ γ) (f : Block → (Fin m → ℝ) → EReal)
    (η w : ℕ → Fin m → ℝ)
    (hzero : ∀ b, IsSubgradientAt (f b) 0 0)
    (hgraph : ∀ b k, IsSubgradientAt (f b) (generatedNormal γ η w b k)
      (generatedPosition η w b k)) :
    Summable (fun k ↦ generatedValues (ℓ := ℓ) f η w k .F 0 +
      generatedValues (ℓ := ℓ) f η w k .J 0) ∧
    Summable (fun k ↦ ∑ a : Fin m,
      FiniteMemory.residual (fun i ↦ generatedHistory (ℓ := ℓ) η w k i a) 0 ^ 2) := by
  exact certificateSequence_summable c (generatedHistory η w) (generatedValues f η w)
    (generatedHistory_shift η w) (generatedValues_shift f η w)
    (generatedValues_nonneg f η w hzero hgraph)
    (generatedValues_gap f η w hzero hgraph)
    (generatedValues_current f η w hzero hgraph)
    (generatedValues_support f η w hgraph)

end ADMM.ConvergenceProof

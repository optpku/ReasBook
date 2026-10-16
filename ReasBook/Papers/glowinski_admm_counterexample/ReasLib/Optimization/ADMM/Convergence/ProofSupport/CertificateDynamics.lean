module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.Convergence.ProofSupport.CertificateStorage
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.Convergence.ProofSupport.StorageDynamics

@[expose] public section

open scoped BigOperators
open ADMM.FiniteMemory

namespace ADMM.ConvergenceProof

noncomputable section

/-- Storage at the predecessor end of a moving generated history. Starting
with such a history avoids evaluating an objective at the arbitrary initial
state, which may lie outside its domain. -/
def certificateSequenceStorage {m ℓ : ℕ} {γ : ℝ} (c : Certificate ℓ γ)
    (Z : ℕ → (Fin (ℓ + 2) × Fin 2) → Fin m → ℝ)
    (Φ : ℕ → Block → Fin (ℓ + 1) → ℝ) (k : ℕ) : ℝ :=
  coordinateQuadraticStorage c.P (fun i ↦ Z k (i.1.succ, i.2)) +
    ∑ b : Block, ∑ j : Fin ℓ,
      lagCoefficient c.lagMinus c.lagPlus b j * Φ k b j.succ

/-- Extend generated finite objective values to the KKT interpolation origin. -/
def predecessorValues {ℓ : ℕ} (Φ : Block → Fin (ℓ + 1) → ℝ)
    (b : Block) (j : Option (Fin ℓ)) : ℝ :=
  match j with
  | none => 0
  | some i => Φ b i.succ

/-- Directed support inequalities at the interpolation origin and generated
points yield the coercive storage bound at every time. -/
theorem certificateSequence_lower {m ℓ : ℕ} {γ : ℝ} (c : Certificate ℓ γ)
    (Z : ℕ → (Fin (ℓ + 2) × Fin 2) → Fin m → ℝ)
    (Φ : ℕ → Block → Fin (ℓ + 1) → ℝ)
    (hgap : ∀ k b i j,
      0 ≤ predecessorValues (Φ k) b i - predecessorValues (Φ k) b j -
        ∑ a : Fin m,
          interpolationNormal γ b j (fun t ↦ Z k (t.1.succ, t.2) a) *
            (interpolationPosition b i (fun t ↦ Z k (t.1.succ, t.2) a) -
              interpolationPosition b j (fun t ↦ Z k (t.1.succ, t.2) a))) (k : ℕ) :
    c.zeta * ∑ a : Fin m, ((Z k (1, 0) a) ^ 2 + (Z k (1, 1) a) ^ 2) ≤
      certificateSequenceStorage c Z Φ k := by
  have h := certificateStorageLowerBound c (fun i ↦ Z k (i.1.succ, i.2))
    (predecessorValues (Φ k)) (fun _ ↦ rfl) (hgap k)
  simpa only [certificateSequenceStorage, predecessorValues, Fin.succ_zero_eq_one,
    sub_nonneg] using h

/-- Consistent moving histories turn the static certificate descent into a
one-step inequality for the storage sequence. -/
theorem certificateSequence_descent {m ℓ : ℕ} {γ : ℝ} (c : Certificate ℓ γ)
    (Z : ℕ → (Fin (ℓ + 2) × Fin 2) → Fin m → ℝ)
    (Φ : ℕ → Block → Fin (ℓ + 1) → ℝ)
    (hZshift : ∀ k (i : Fin (ℓ + 1) × Fin 2), Z (k + 1) (i.1.succ, i.2) = Z k (i.1.castSucc, i.2))
    (hΦshift : ∀ k b (j : Fin ℓ), Φ (k + 1) b j.succ = Φ k b j.castSucc)
    (hcurrent : ∀ k b,
      Φ k b 0 ≤ ∑ a : Fin m,
        graphNormal γ b (fun i ↦ Z k i a) 0 * graphPosition b (fun i ↦ Z k i a) 0)
    (hsupport : ∀ k b i j,
      Φ k b j - Φ k b i ≤ ∑ a : Fin m,
        graphNormal γ b (fun t ↦ Z k t a) j *
          (graphPosition b (fun t ↦ Z k t a) j -
            graphPosition b (fun t ↦ Z k t a) i)) (k : ℕ) :
    certificateSequenceStorage c Z Φ (k + 1) +
      c.omega * (Φ k .F 0 + Φ k .J 0) +
      c.epsilon * ∑ a : Fin m, residual (fun i ↦ Z k i a) 0 ^ 2 ≤
      certificateSequenceStorage c Z Φ k := by
  have h := certificateStorageDescent c (Z k) (Φ k) (hcurrent k) (hsupport k)
  have hnext : certificateSequenceStorage c Z Φ (k + 1) =
      coordinateQuadraticStorage c.P (fun i ↦ Z k (i.1.castSucc, i.2)) +
        ∑ b : Block, ∑ j : Fin ℓ,
          lagCoefficient c.lagMinus c.lagPlus b j * Φ k b j.castSucc := by
    simp only [certificateSequenceStorage, hZshift, hΦshift]
  rw [hnext]
  dsimp only [certificateSequenceStorage]
  linarith

/-- The two matrix tests and generated support inequalities imply summability
of the merit values and the squared residual coordinates. -/
theorem certificateSequence_summable {m ℓ : ℕ} {γ : ℝ} (c : Certificate ℓ γ)
    (Z : ℕ → (Fin (ℓ + 2) × Fin 2) → Fin m → ℝ)
    (Φ : ℕ → Block → Fin (ℓ + 1) → ℝ)
    (hZshift : ∀ k (i : Fin (ℓ + 1) × Fin 2), Z (k + 1) (i.1.succ, i.2) = Z k (i.1.castSucc, i.2))
    (hΦshift : ∀ k b (j : Fin ℓ), Φ (k + 1) b j.succ = Φ k b j.castSucc)
    (hΦ : ∀ k b j, 0 ≤ Φ k b j)
    (hgap : ∀ k b i j,
      0 ≤ predecessorValues (Φ k) b i - predecessorValues (Φ k) b j -
        ∑ a : Fin m,
          interpolationNormal γ b j (fun t ↦ Z k (t.1.succ, t.2) a) *
            (interpolationPosition b i (fun t ↦ Z k (t.1.succ, t.2) a) -
              interpolationPosition b j (fun t ↦ Z k (t.1.succ, t.2) a)))
    (hcurrent : ∀ k b,
      Φ k b 0 ≤ ∑ a : Fin m,
        graphNormal γ b (fun i ↦ Z k i a) 0 * graphPosition b (fun i ↦ Z k i a) 0)
    (hsupport : ∀ k b i j,
      Φ k b j - Φ k b i ≤ ∑ a : Fin m,
        graphNormal γ b (fun t ↦ Z k t a) j *
          (graphPosition b (fun t ↦ Z k t a) j -
            graphPosition b (fun t ↦ Z k t a) i)) :
    Summable (fun k ↦ Φ k .F 0 + Φ k .J 0) ∧
      Summable (fun k ↦ ∑ a : Fin m, residual (fun i ↦ Z k i a) 0 ^ 2) := by
  have hU : ∀ k, 0 ≤ certificateSequenceStorage c Z Φ k := by
    intro k
    apply le_trans _ (certificateSequence_lower c Z Φ hgap k)
    exact mul_nonneg c.zeta_pos.le (Finset.sum_nonneg fun a _ ↦
      add_nonneg (sq_nonneg _) (sq_nonneg _))
  exact storage_two_dissipations_summable c.omega_pos c.epsilon_pos hU
    (fun k ↦ add_nonneg (hΦ k .F 0) (hΦ k .J 0))
    (fun k ↦ Finset.sum_nonneg fun a _ ↦ sq_nonneg _)
    (certificateSequence_descent c Z Φ hZshift hΦshift hcurrent hsupport)

end

end ADMM.ConvergenceProof

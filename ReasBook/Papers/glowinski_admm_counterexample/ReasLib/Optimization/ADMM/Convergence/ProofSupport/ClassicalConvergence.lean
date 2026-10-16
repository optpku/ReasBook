module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.Convergence.ProofSupport.OrbitEnergy
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.Convergence.ProofSupport.GeneratedHistory

@[expose] public section

open ADMM.FiniteMemory

namespace ADMM.ConvergenceProof

/-- A symmetric Young bound with an arbitrary real coefficient, in the
coordinate inner product used by the normalized ADMM orbit. -/
lemma coordinate_young_abs {m : ℕ} (a : ℝ) (d r : Fin m → ℝ) :
    2 * a * dotProduct d r ≤ |a| * (coordinateSquare d + coordinateSquare r) := by
  have hp := coordinateSquare_nonneg (d + r)
  have hm := coordinateSquare_nonneg (d - r)
  simp only [coordinateSquare, add_dotProduct, dotProduct_add,
    sub_dotProduct, dotProduct_sub, dotProduct_comm r d] at hp hm
  dsimp only [coordinateSquare]
  by_cases ha : 0 ≤ a
  · rw [abs_of_nonneg ha]
    nlinarith [mul_nonneg ha hm]
  · have ha' : a ≤ 0 := le_of_not_ge ha
    rw [abs_of_nonpos ha']
    nlinarith [mul_nonneg (neg_nonneg.mpr ha') hp]

/-- Classical one-step descent, using monotonicity between two consecutive
second-block graph points. The residual from the preceding step is added to
the usual primal-dual energy. -/
lemma classical_energy_step {m : ℕ} {γ : ℝ} (hγ : 0 ≤ γ)
    (η₀ η₁ w₀ w₁ rprev : Fin m → ℝ)
    (hpair : 0 ≤
      dotProduct (η₀ - γ • w₀ - (η₁ + (w₁ - w₀))) (η₁ + (w₁ - w₀)) +
        dotProduct (γ • w₀ + (w₁ - w₀)) η₁)
    (hadj : 0 ≤ dotProduct (η₁ - η₀) ((w₁ - w₀) + (γ - 1) • rprev)) :
    (γ ^ 2 * coordinateSquare w₁ + γ * coordinateSquare η₁ +
        γ * |γ - 1| * coordinateSquare (w₁ - w₀)) +
      γ * (1 - |γ - 1|) * coordinateSquare (η₁ - η₀) +
      γ * (2 - γ - |γ - 1|) * coordinateSquare (w₁ - w₀) ≤
    γ ^ 2 * coordinateSquare w₀ + γ * coordinateSquare η₀ +
      γ * |γ - 1| * coordinateSquare rprev := by
  have heq := reduced_energy_identity γ η₀ η₁ w₀ w₁
  have hy := coordinate_young_abs (γ - 1) (η₁ - η₀) rprev
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul] at hadj
  nlinarith [mul_nonneg hγ hpair, mul_nonneg hγ hadj,
    mul_le_mul_of_nonneg_left hy hγ]

/-- Below `3/2`, the classical energy gives square-summable residuals and a
uniform coordinate bound for the entire normalized trajectory. -/
theorem classical_residual_summable_bounded {m : ℕ} {γ : ℝ}
    (hγ : 0 < γ) (hγupper : γ < 3 / 2)
    (f : Block → (Fin m → ℝ) → EReal) (η w : ℕ → Fin m → ℝ)
    (hzero : ∀ b, IsSubgradientAt (f b) 0 0)
    (hgraph : ∀ b k, IsSubgradientAt (f b) (generatedNormal γ η w b k)
      (generatedPosition η w b k)) :
    Summable (fun k ↦ coordinateSquare (w (k + 1) - w k)) ∧
      ∃ C : ℝ, ∀ k, coordinateSquare (η k) + coordinateSquare (w k) ≤ C := by
  let r := fun k ↦ w (k + 1) - w k
  let E := fun k ↦ γ ^ 2 * coordinateSquare (w k) + γ * coordinateSquare (η k)
  let V := fun k ↦ E (k + 1) + γ * |γ - 1| * coordinateSquare (r k)
  have hdpos : 0 < γ * (1 - |γ - 1|) := by
    apply mul_pos hγ
    rw [sub_pos, abs_lt]
    constructor <;> linarith
  have hrpos : 0 < γ * (2 - γ - |γ - 1|) := by
    apply mul_pos hγ
    rw [sub_pos, abs_lt]
    constructor <;> linarith
  have hpair (k : ℕ) : 0 ≤
      dotProduct (η k - γ • w k - (η (k + 1) + r k)) (η (k + 1) + r k) +
        dotProduct (γ • w k + r k) (η (k + 1)) := by
    have hf := subgradient_monotone (hgraph .F k) (hzero .F)
    have hj := subgradient_monotone (hgraph .J k) (hzero .J)
    simpa only [sub_zero, generatedNormal, generatedPosition, r] using add_nonneg hf hj
  have hadj (k : ℕ) : 0 ≤ dotProduct (η (k + 1 + 1) - η (k + 1))
      (r (k + 1) + (γ - 1) • r k) := by
    have h := subgradient_monotone (hgraph .J (k + 1)) (hgraph .J k)
    have hnormal : generatedNormal γ η w .J (k + 1) - generatedNormal γ η w .J k =
        r (k + 1) + (γ - 1) • r k := by
      dsimp [generatedNormal, r]
      module
    rw [hnormal, dotProduct_comm] at h
    exact h
  have hE (k : ℕ) : 0 ≤ E k := by
    exact add_nonneg (mul_nonneg (sq_nonneg _) (coordinateSquare_nonneg _))
      (mul_nonneg hγ.le (coordinateSquare_nonneg _))
  have hV (k : ℕ) : 0 ≤ V k :=
    add_nonneg (hE _) (mul_nonneg (mul_nonneg hγ.le (abs_nonneg _)) (coordinateSquare_nonneg _))
  have hstep (k : ℕ) : V (k + 1) +
      (γ * (1 - |γ - 1|)) * coordinateSquare (η (k + 1 + 1) - η (k + 1)) +
      (γ * (2 - γ - |γ - 1|)) * coordinateSquare (r (k + 1)) ≤ V k :=
    classical_energy_step hγ.le _ _ _ _ _ (hpair (k + 1)) (hadj k)
  have hs := storage_two_dissipations_summable hdpos hrpos hV
    (fun _ ↦ coordinateSquare_nonneg _) (fun _ ↦ coordinateSquare_nonneg _) hstep
  have hr : Summable (fun k ↦ coordinateSquare (r k)) :=
    (summable_nat_add_iff 1).mp hs.2
  have hmono : Antitone V := by
    apply antitone_nat_of_succ_le
    intro k
    linarith [hstep k,
      mul_nonneg hdpos.le (coordinateSquare_nonneg (η (k + 1 + 1) - η (k + 1))),
      mul_nonneg hrpos.le (coordinateSquare_nonneg (r (k + 1)))]
  have hEb (k : ℕ) : E k ≤ max (E 0) (V 0) := by
    cases k with
    | zero => exact le_max_left _ _
    | succ k =>
      have hEV : E (k + 1) ≤ V k :=
        le_add_of_nonneg_right (mul_nonneg (mul_nonneg hγ.le (abs_nonneg _))
          (coordinateSquare_nonneg _))
      exact hEV.trans ((hmono (Nat.zero_le k)).trans (le_max_right _ _))
  refine ⟨hr, max (E 0) (V 0) / γ + max (E 0) (V 0) / γ ^ 2, ?_⟩
  intro k
  have hη : coordinateSquare (η k) ≤ max (E 0) (V 0) / γ := by
    apply (le_div_iff₀ hγ).2
    have hb := hEb k
    dsimp [E] at hb
    nlinarith [mul_nonneg (sq_nonneg γ) (coordinateSquare_nonneg (w k))]
  have hw : coordinateSquare (w k) ≤ max (E 0) (V 0) / γ ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hγ)).2
    have hb := hEb k
    dsimp [E] at hb
    nlinarith [mul_nonneg hγ.le (coordinateSquare_nonneg (η k))]
  exact add_le_add hη hw

end ADMM.ConvergenceProof

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.Proximal
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.ConsensusBridge

@[expose] public section

namespace ADMM

/-- A supporting plane with normal `center - x` certifies the finite proximal
minimum. No closedness assumption is needed for this sufficient condition. -/
theorem isProxPoint_of_subgradient {n : ℕ} {φ : (Fin n → ℝ) → EReal}
    {center x : Fin n → ℝ} (hx : IsSubgradientAt φ (center - x) x) :
    IsProxPoint φ center x := by
  obtain ⟨c, hc, hs⟩ := hx
  refine ⟨c + dotProduct (x - center) (x - center) / 2, ?_, ?_⟩
  · change φ x + ((dotProduct (x - center) (x - center) / 2 : ℝ) : EReal) = _
    rw [hc, ← EReal.coe_add]
  · intro y
    have hnonneg : 0 ≤ dotProduct (y - x) (y - x) :=
      Finset.sum_nonneg (fun i _ => mul_self_nonneg ((y - x) i))
    have hquad : dotProduct (x - center) (x - center) / 2 ≤
        dotProduct (center - x) (y - x) +
          dotProduct (y - center) (y - center) / 2 := by
      simp only [sub_dotProduct, dotProduct_sub] at hnonneg ⊢
      rw [dotProduct_comm y x] at hnonneg
      rw [dotProduct_comm center y, dotProduct_comm center x]
      nlinarith
    calc
      φ x + ((dotProduct (x - center) (x - center) / 2 : ℝ) : EReal) =
          ((c + dotProduct (x - center) (x - center) / 2 : ℝ) : EReal) := by
            rw [hc, ← EReal.coe_add]
      _ ≤ ((c + dotProduct (center - x) (y - x) +
          dotProduct (y - center) (y - center) / 2 : ℝ) : EReal) := by
            exact EReal.coe_le_coe_iff.mpr (by linarith)
      _ ≤ φ y + ((dotProduct (y - center) (y - center) / 2 : ℝ) : EReal) := by
            simpa only [hc, ← EReal.coe_add, add_comm] using
              add_le_add_right (hs y)
                (((dotProduct (y - center) (y - center) / 2 : ℝ) : EReal))

/-- Completing the square for the first unit-penalty consensus block. -/
private lemma first_quadratic_decomposition {n : ℕ} (x y dual : Fin n → ℝ) :
    dotProduct (x - (y - dual)) (x - (y - dual)) / 2 =
      (dotProduct dual (x - y) + dotProduct (x - y) (x - y) / 2) +
        dotProduct dual dual / 2 := by
  have hd : x - (y - dual) = (x - y) + dual := by module
  rw [hd]
  simp only [add_dotProduct, dotProduct_add]
  rw [dotProduct_comm (x - y) dual]
  ring

/-- Completing the square for the second unit-penalty consensus block. -/
private lemma second_quadratic_decomposition {n : ℕ} (y x dual : Fin n → ℝ) :
    dotProduct (y - (x + dual)) (y - (x + dual)) / 2 =
      (dotProduct dual (x - y) + dotProduct (x - y) (x - y) / 2) +
        dotProduct dual dual / 2 := by
  have hd : y - (x + dual) = -((x - y) + dual) := by module
  rw [hd, neg_dotProduct, dotProduct_neg, neg_neg]
  simp only [add_dotProduct, dotProduct_add]
  rw [dotProduct_comm (x - y) dual]
  ring

/-- A proximal first update minimizes the consensus augmented objective. The
additive square-completion constant is finite, even for infinite objectives. -/
theorem first_augmented_minimum_of_prox {n : ℕ} {φ : (Fin n → ℝ) → EReal}
    {x y dual : Fin n → ℝ} (hx : IsProxPoint φ (y - dual) x) (z : Fin n → ℝ) :
    φ x + ((dotProduct dual (x - y) + dotProduct (x - y) (x - y) / 2 : ℝ) : EReal) ≤
      φ z + ((dotProduct dual (z - y) + dotProduct (z - y) (z - y) / 2 : ℝ) : EReal) := by
  obtain ⟨_, _, hmin⟩ := hx
  have h := hmin z
  change φ x + ((dotProduct (x - (y - dual)) (x - (y - dual)) / 2 : ℝ) : EReal) ≤
    φ z + ((dotProduct (z - (y - dual)) (z - (y - dual)) / 2 : ℝ) : EReal) at h
  have heq (t : Fin n → ℝ) :
      φ t + ((dotProduct (t - (y - dual)) (t - (y - dual)) / 2 : ℝ) : EReal) =
        (φ t + ((dotProduct dual (t - y) + dotProduct (t - y) (t - y) / 2 : ℝ) : EReal)) +
          ((dotProduct dual dual / 2 : ℝ) : EReal) := by
    rw [first_quadratic_decomposition, EReal.coe_add, add_assoc]
  rw [heq x, heq z] at h
  exact (EReal.addLECancellable_coe (dotProduct dual dual / 2)).add_le_add_iff_right.mp h

/-- A proximal second update minimizes the consensus augmented objective. -/
theorem second_augmented_minimum_of_prox {n : ℕ} {φ : (Fin n → ℝ) → EReal}
    {y x dual : Fin n → ℝ} (hy : IsProxPoint φ (x + dual) y) (z : Fin n → ℝ) :
    φ y + ((dotProduct dual (x - y) + dotProduct (x - y) (x - y) / 2 : ℝ) : EReal) ≤
      φ z + ((dotProduct dual (x - z) + dotProduct (x - z) (x - z) / 2 : ℝ) : EReal) := by
  obtain ⟨_, _, hmin⟩ := hy
  have h := hmin z
  change φ y + ((dotProduct (y - (x + dual)) (y - (x + dual)) / 2 : ℝ) : EReal) ≤
    φ z + ((dotProduct (z - (x + dual)) (z - (x + dual)) / 2 : ℝ) : EReal) at h
  have heq (t : Fin n → ℝ) :
      φ t + ((dotProduct (t - (x + dual)) (t - (x + dual)) / 2 : ℝ) : EReal) =
        (φ t + ((dotProduct dual (x - t) + dotProduct (x - t) (x - t) / 2 : ℝ) : EReal)) +
          ((dotProduct dual dual / 2 : ℝ) : EReal) := by
    rw [second_quadratic_decomposition, EReal.coe_add, add_assoc]
  rw [heq y, heq z] at h
  exact (EReal.addLECancellable_coe (dotProduct dual dual / 2)).add_le_add_iff_right.mp h

end ADMM

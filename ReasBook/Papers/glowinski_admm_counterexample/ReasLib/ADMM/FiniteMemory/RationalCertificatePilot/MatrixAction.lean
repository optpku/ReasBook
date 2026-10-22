/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificatePilot.MatrixAssembly

@[expose] public section

namespace ADMM.FiniteMemory.Reconstruction.MatrixAssembly

/-- Constant history in one of the two scalar coordinates. -/
def constantVector {k : ℕ} (a : Fin 2) : (Fin k × Fin 2) → ℚ :=
  fun i ↦ if i.2 = a then 1 else 0

/-- The Kronecker entries sum to the corresponding constant history. -/
theorem sum_unitVector {k : ℕ} (a : Fin 2) (i : Fin k × Fin 2) :
    (∑ t : Fin k, unitVector (t, a) i) = constantVector a i := by
  rcases i with ⟨i, q⟩
  by_cases h : q = a <;> simp [unitVector, constantVector, Prod.mk.injEq, h]

theorem sum_graphPosition {ℓ : ℕ} (b : Block) (d : Fin (ℓ + 1)) (a : Fin 2) :
    (∑ t : Fin (ℓ + 2), ADMM.FiniteMemory.graphPosition b (unitVector (t, a)) d) =
      ADMM.FiniteMemory.graphPosition b (constantVector a) d := by
  cases b <;>
    simp only [ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_unitVector]

theorem sum_graphNormal {ℓ : ℕ} (γ : ℚ) (b : Block) (d : Fin (ℓ + 1)) (a : Fin 2) :
    (∑ t : Fin (ℓ + 2), graphNormal γ b (unitVector (t, a)) d) =
      graphNormal γ b (constantVector a) d := by
  cases b <;>
    simp only [graphNormal, ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_unitVector]

/-- Multiplication by constant modes needs only a single scalar column from each block. -/
theorem mul_constantModes {ρ : Type*} {k : ℕ}
    (K : Matrix ρ (Fin k × Fin 2) ℚ) (i : ρ) (a : Fin 2) :
    (K * constantModes k) i a = ∑ t : Fin k, K i (t, a) := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp [constantModes]

/-- A symmetric bilinear entry against one constant history. -/
def actionProduct {k : ℕ} (f g : ((Fin k × Fin 2) → ℚ) → ℚ)
    (i : Fin k × Fin 2) (a : Fin 2) : ℚ :=
  (f (unitVector i) * g (constantVector a) +
    f (constantVector a) * g (unitVector i)) / 2

theorem sum_productEntry {k : ℕ} (f g : ((Fin k × Fin 2) → ℚ) → ℚ)
    (i : Fin k × Fin 2) (a : Fin 2)
    (hf : (∑ t : Fin k, f (unitVector (t, a))) = f (constantVector a))
    (hg : (∑ t : Fin k, g (unitVector (t, a))) = g (constantVector a)) :
    (∑ t : Fin k, productEntry f g i (t, a)) = actionProduct f g i a := by
  simp only [productEntry, actionProduct, ← Finset.sum_div, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul, hf, hg]

theorem sum_graphPosition_diff {ℓ : ℕ} (b : Block) (d e : Fin (ℓ + 1)) (a : Fin 2) :
    (∑ t : Fin (ℓ + 2), (ADMM.FiniteMemory.graphPosition b (unitVector (t, a)) d -
      ADMM.FiniteMemory.graphPosition b (unitVector (t, a)) e)) =
    ADMM.FiniteMemory.graphPosition b (constantVector a) d -
      ADMM.FiniteMemory.graphPosition b (constantVector a) e := by
  rw [Finset.sum_sub_distrib, sum_graphPosition, sum_graphPosition]

theorem sum_residual {ℓ : ℕ} (d : Fin (ℓ + 1)) (a : Fin 2) :
    (∑ t : Fin (ℓ + 2), ADMM.FiniteMemory.residual (unitVector (t, a)) d) =
      ADMM.FiniteMemory.residual (constantVector a) d := by
  simp only [ADMM.FiniteMemory.residual, Finset.sum_sub_distrib, sum_unitVector]

theorem sum_product_graph {ℓ : ℕ} (γ : ℚ) (b : Block) (n d : Fin (ℓ + 1))
    (i : Fin (ℓ + 2) × Fin 2) (a : Fin 2) :
    (∑ t : Fin (ℓ + 2), productEntry (fun Z ↦ graphNormal γ b Z n)
      (fun Z ↦ ADMM.FiniteMemory.graphPosition b Z d) i (t, a)) =
    actionProduct (fun Z ↦ graphNormal γ b Z n)
      (fun Z ↦ ADMM.FiniteMemory.graphPosition b Z d) i a :=
  sum_productEntry _ _ i a (sum_graphNormal γ b n a) (sum_graphPosition b d a)

theorem sum_product_graph_diff {ℓ : ℕ} (γ : ℚ) (b : Block) (n d e : Fin (ℓ + 1))
    (i : Fin (ℓ + 2) × Fin 2) (a : Fin 2) :
    (∑ t : Fin (ℓ + 2), productEntry (fun Z ↦ graphNormal γ b Z n)
      (fun Z ↦ ADMM.FiniteMemory.graphPosition b Z d -
        ADMM.FiniteMemory.graphPosition b Z e) i (t, a)) =
    actionProduct (fun Z ↦ graphNormal γ b Z n)
      (fun Z ↦ ADMM.FiniteMemory.graphPosition b Z d -
        ADMM.FiniteMemory.graphPosition b Z e) i a :=
  sum_productEntry _ _ i a (sum_graphNormal γ b n a) (sum_graphPosition_diff b d e a)

theorem sum_product_residual {ℓ : ℕ} (d : Fin (ℓ + 1))
    (i : Fin (ℓ + 2) × Fin 2) (a : Fin 2) :
    (∑ t : Fin (ℓ + 2), productEntry (fun Z ↦ ADMM.FiniteMemory.residual Z d)
      (fun Z ↦ ADMM.FiniteMemory.residual Z d) i (t, a)) =
    actionProduct (fun Z ↦ ADMM.FiniteMemory.residual Z d)
      (fun Z ↦ ADMM.FiniteMemory.residual Z d) i a :=
  sum_productEntry _ _ i a (sum_residual d a) (sum_residual d a)

/-- Direct action of the supply matrix on constant modes, without constructing Q. -/
def supplyActionEntry {ℓ : ℕ} (c : RationalCase ℓ) (γ : ℚ)
    (i : Fin (ℓ + 2) × Fin 2) (a : Fin 2) : ℚ :=
  c.omega *
    (actionProduct (fun Z ↦ graphNormal γ .F Z 0)
        (fun Z ↦ ADMM.FiniteMemory.graphPosition .F Z 0) i a +
      actionProduct (fun Z ↦ graphNormal γ .J Z 0)
        (fun Z ↦ ADMM.FiniteMemory.graphPosition .J Z 0) i a) +
    c.epsilon * actionProduct (fun Z ↦ ADMM.FiniteMemory.residual Z 0)
      (fun Z ↦ ADMM.FiniteMemory.residual Z 0) i a +
    ∑ b : Block, ∑ d : Fin ℓ,
      (lagMinusValue c b d * actionProduct (fun Z ↦ graphNormal γ b Z 0)
        (fun Z ↦ ADMM.FiniteMemory.graphPosition b Z 0 -
          ADMM.FiniteMemory.graphPosition b Z d.succ) i a +
       lagPlusValue c b d * actionProduct (fun Z ↦ graphNormal γ b Z d.succ)
        (fun Z ↦ ADMM.FiniteMemory.graphPosition b Z d.succ -
          ADMM.FiniteMemory.graphPosition b Z 0) i a)

private theorem sum_swap {α β δ : Type*} [Fintype α] [Fintype β] [Fintype δ]
    (f : α → β → δ → ℚ) : (∑ a, ∑ b, ∑ d, f a b d) = ∑ b, ∑ d, ∑ a, f a b d := by
  rw [Finset.sum_comm]
  congr 1
  ext b
  rw [Finset.sum_comm]

theorem sum_weighted_graph_diff {ℓ : ℕ} (γ : ℚ)
    (v : Block → Fin ℓ → ℚ) (n d e : Fin ℓ → Fin (ℓ + 1))
    (i : Fin (ℓ + 2) × Fin 2) (a : Fin 2) :
    (∑ t : Fin (ℓ + 2), ∑ b : Block, ∑ r : Fin ℓ,
      v b r * productEntry (fun Z ↦ graphNormal γ b Z (n r))
        (fun Z ↦ ADMM.FiniteMemory.graphPosition b Z (d r) -
          ADMM.FiniteMemory.graphPosition b Z (e r)) i (t, a)) =
    ∑ b : Block, ∑ r : Fin ℓ,
      v b r * actionProduct (fun Z ↦ graphNormal γ b Z (n r))
        (fun Z ↦ ADMM.FiniteMemory.graphPosition b Z (d r) -
          ADMM.FiniteMemory.graphPosition b Z (e r)) i a := by
  rw [sum_swap]
  simp only [← Finset.mul_sum, sum_product_graph_diff]

theorem supplyConstantModes_factored {ℓ : ℕ} (c : RationalCase ℓ) (γ : ℚ)
    (i : Fin (ℓ + 2) × Fin 2) (a : Fin 2) :
    supplyConstantModes c γ i a = supplyActionEntry c γ i a := by
  rw [supplyConstantModes, mul_constantModes]
  simp_rw [supplyMatrix_factored]
  unfold supplyEntry supplyActionEntry
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [sum_weighted_graph_diff, sum_product_graph, sum_product_residual]

/-- The first constant mode only sees the nearest eta difference. -/
theorem supplyConstantModes_zero {ℓ : ℕ} (c : RationalCase ℓ) (γ : ℚ)
    (i : Fin (ℓ + 2) × Fin 2) :
    supplyConstantModes c γ i 0 =
      c.omega / 2 * (unitVector i (1, 0) - unitVector i (0, 0)) := by
  rw [supplyConstantModes_factored]
  simp [supplyActionEntry, sum_block, actionProduct, constantVector,
    graphNormal, ADMM.FiniteMemory.graphPosition, ADMM.FiniteMemory.residual]
  ring

/-- Directed lag sign for the second constant mode. -/
def actionLag {ℓ : ℕ} (c : RationalCase ℓ) (b : Block) (d : Fin ℓ) : ℚ :=
  match b with
  | .F => lagPlusValue c b d - lagMinusValue c b d
  | .J => lagMinusValue c b d - lagPlusValue c b d

/-- The second constant mode uses positions only, since constant-history position differences vanish. -/
theorem supplyConstantModes_one {ℓ : ℕ} (c : RationalCase ℓ) (γ : ℚ)
    (i : Fin (ℓ + 2) × Fin 2) :
    supplyConstantModes c γ i 1 = γ / 2 *
      (-c.omega * ADMM.FiniteMemory.residual (unitVector i) 0 +
        ∑ b : Block, ∑ d : Fin ℓ, actionLag c b d *
          (ADMM.FiniteMemory.graphPosition b (unitVector i) 0 -
            ADMM.FiniteMemory.graphPosition b (unitVector i) d.succ)) := by
  rw [supplyConstantModes_factored]
  simp only [supplyActionEntry, sum_block]
  simp only [actionProduct, constantVector, graphNormal, ADMM.FiniteMemory.graphPosition,
    ADMM.FiniteMemory.residual, Prod.snd, ↓reduceIte, sub_self, mul_zero, zero_sub,
    zero_add, add_zero, mul_one, zero_mul, zero_div, Fin.isValue, one_ne_zero,
    zero_ne_one, actionLag]
  simp only [mul_add, Finset.mul_sum]
  congr 1
  · ring
  · congr 1 <;> apply Finset.sum_congr rfl <;> intro d hd <;> ring

end ADMM.FiniteMemory.Reconstruction.MatrixAssembly

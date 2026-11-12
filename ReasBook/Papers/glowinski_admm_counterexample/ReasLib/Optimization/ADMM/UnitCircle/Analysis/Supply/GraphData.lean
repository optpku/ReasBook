/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Supply.Total

@[expose] public section

open scoped BigOperators
open ADMM.ConvergenceProof

namespace ADMM.UnitCircle.Supply

/-- Finite-valued graph interpolation data. These are only the origin and
pairwise convex support inequalities; no summed supply inequality is assumed. -/
structure GraphData {m : ℕ} (x g : ℕ → Fin m → ℝ) where
  value : ℕ → ℝ
  nonneg : ∀ k, 0 ≤ value k
  origin_upper : ∀ k, value k ≤ dotProduct (g k) (x k)
  support : ∀ i j, value i - value j ≤ dotProduct (g i) (x i - x j)


/-- A common scalar scaling preserves all graph support inequalities, with
squared scaling of the potentials. It aligns either time-index convention for
the discounted proximal operator. -/
noncomputable def GraphData.scale {m : ℕ} {x g : ℕ → Fin m → ℝ}
    (D : GraphData x g) (a : ℝ) :
    GraphData (fun k ↦ a • x k) (fun k ↦ a • g k) where
  value k := a ^ 2 * D.value k
  nonneg k := mul_nonneg (sq_nonneg a) (D.nonneg k)
  origin_upper k := by
    have h := mul_le_mul_of_nonneg_left (D.origin_upper k) (sq_nonneg a)
    simpa only [smul_dotProduct, dotProduct_smul, smul_eq_mul, pow_two, mul_assoc] using h
  support i j := by
    have h := mul_le_mul_of_nonneg_left (D.support i j) (sq_nonneg a)
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
      smul_eq_mul] at h ⊢
    nlinarith

/-- The supremum of the recorded supporting planes and the zero plane. Its
values at every recorded graph point are fixed by the interpolation data. -/
noncomputable def supportObjective {m : ℕ} {x g : ℕ → Fin m → ℝ}
    (D : GraphData x g) (z : Fin m → ℝ) : EReal :=
  ⨆ i : Option ℕ, match i with
    | none => (0 : EReal)
    | some k => ((D.value k + dotProduct (g k) (z - x k) : ℝ) : EReal)

lemma supportObjective_value {m : ℕ} {x g : ℕ → Fin m → ℝ}
    (D : GraphData x g) (k : ℕ) : supportObjective D (x k) = (D.value k : EReal) := by
  apply le_antisymm
  · apply iSup_le
    intro i
    cases i with
    | none =>
      change (0 : EReal) ≤ (D.value k : EReal)
      exact_mod_cast D.nonneg k
    | some i =>
      have h := D.support i k
      simp only [dotProduct_sub] at h ⊢
      apply EReal.coe_le_coe_iff.mpr
      linarith
  · have h := le_iSup (fun i : Option ℕ ↦ match i with
        | none => (0 : EReal)
        | some i => ((D.value i + dotProduct (g i) (x k - x i) : ℝ) : EReal))
        (some k)
    simpa only [supportObjective, sub_self, dotProduct_zero, add_zero] using h

lemma supportObjective_zero {m : ℕ} {x g : ℕ → Fin m → ℝ}
    (D : GraphData x g) : supportObjective D 0 = 0 := by
  apply le_antisymm
  · apply iSup_le
    intro i
    cases i with
    | none => exact le_rfl
    | some i =>
      have h := D.origin_upper i
      simp only [zero_sub, dotProduct_neg]
      exact_mod_cast (show D.value i + -(dotProduct (g i) (x i)) ≤ 0 by linarith)
  · exact le_iSup (fun i : Option ℕ ↦ match i with
      | none => (0 : EReal)
      | some i => ((D.value i + dotProduct (g i) (0 - x i) : ℝ) : EReal)) none

/-- The interpolating supremum has the zero KKT graph point. -/
theorem supportObjective_zero_graph {m : ℕ} {x g : ℕ → Fin m → ℝ}
    (D : GraphData x g) : IsSubgradientAt (supportObjective D) 0 0 := by
  refine ⟨0, supportObjective_zero D, ?_⟩
  intro z
  rw [supportObjective_zero]
  simp only [zero_dotProduct, EReal.coe_zero, add_zero]
  exact le_iSup (fun i : Option ℕ ↦ match i with
    | none => (0 : EReal)
    | some i => ((D.value i + dotProduct (g i) (z - x i) : ℝ) : EReal)) none

/-- Each recorded supporting plane is an actual subgradient of the supremum. -/
theorem supportObjective_graph {m : ℕ} {x g : ℕ → Fin m → ℝ}
    (D : GraphData x g) (k : ℕ) : IsSubgradientAt (supportObjective D) (g k) (x k) := by
  refine ⟨D.value k, supportObjective_value D k, ?_⟩
  intro z
  rw [supportObjective_value, ← EReal.coe_add]
  exact le_iSup (fun i : Option ℕ ↦ match i with
    | none => (0 : EReal)
    | some i => ((D.value i + dotProduct (g i) (z - x i) : ℝ) : EReal)) (some k)

/-- Convex supply also applies directly to finite graph interpolation data.
This form covers the scaled proximal family in the causal homotopy argument. -/
theorem discounted_supply_of_graphData {m ℓ : ℕ} (c : LagWeights ℓ) (b : Fin 2)
    {x g : ℕ → Fin m → ℝ} {α : ℝ} (D : GraphData x g)
    (hx : Summable (fun k ↦ timeWeight α k * coordinateSquare (x k)))
    (hg : Summable (fun k ↦ timeWeight α k * coordinateSquare (g k)))
    (hcorrection : |discountCorrection c b α| ≤ c.omega / 2) :
    0 ≤ (c.omega / 2) * (∑' k, timeWeight α k * dotProduct (g k) (x k)) ∧
      (c.omega / 2) * (∑' k, timeWeight α k * dotProduct (g k) (x k)) ≤
        ∑' k, timeWeight α k * blockSupply c b x g k :=
  discounted_convex_supply c b (supportObjective_zero_graph D)
    (supportObjective_graph D) hx hg hcorrection

end ADMM.UnitCircle.Supply

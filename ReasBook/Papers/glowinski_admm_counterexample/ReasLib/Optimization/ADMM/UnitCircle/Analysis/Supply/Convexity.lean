/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.Convergence.ProofSupport.TiltedValues
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.Convergence.ProofSupport.OrbitEnergy
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Symbol
public import Mathlib.Topology.Algebra.InfiniteSum.Real

@[expose] public section

open scoped BigOperators
open ADMM.ConvergenceProof

namespace ADMM.UnitCircle.Supply

/-- The graph height after subtracting the minimum at the KKT origin. -/
noncomputable def graphValue {m : ℕ} (f : (Fin m → ℝ) → EReal)
    (x : Fin m → ℝ) : ℝ := (f x).toReal - (f 0).toReal

/-- The KKT origin bounds every finite graph height between zero and its
origin monotonicity pairing. -/
theorem graphValue_bounds {m : ℕ} {f : (Fin m → ℝ) → EReal}
    (hzero : IsSubgradientAt f 0 0) {x g : Fin m → ℝ}
    (hx : IsSubgradientAt f g x) :
    0 ≤ graphValue f x ∧ graphValue f x ≤ dotProduct g x := by
  have h₀ := subgradient_support_real hzero hx
  have h₁ := subgradient_support_real hx hzero
  simp only [zero_dotProduct, add_zero, zero_sub, dotProduct_neg] at h₀ h₁
  constructor <;> dsimp only [graphValue] <;> linarith

/-- Two directed lag comparisons have the signed potential difference used
in the discounted multiplier inequality. -/
theorem directed_lag_lower {m : ℕ} {f : (Fin m → ℝ) → EReal}
    {x y g h : Fin m → ℝ} (hx : IsSubgradientAt f g x)
    (hy : IsSubgradientAt f h y) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a - b) * (graphValue f x - graphValue f y) ≤
      a * dotProduct g (x - y) + b * dotProduct h (y - x) := by
  have hxy := subgradient_support_real hx hy
  have hyx := subgradient_support_real hy hx
  have h₁ : graphValue f x - graphValue f y ≤ dotProduct g (x - y) := by
    dsimp only [graphValue]
    simp only [dotProduct_sub] at hxy ⊢
    linarith
  have h₂ : graphValue f y - graphValue f x ≤ dotProduct h (y - x) := by
    dsimp only [graphValue]
    simp only [dotProduct_sub] at hyx ⊢
    linarith
  have h₁' := mul_le_mul_of_nonneg_left h₁ ha
  have h₂' := mul_le_mul_of_nonneg_left h₂ hb
  nlinarith

/-- A one-sided sequence is extended by the KKT origin before its first term. -/
def zeroDelay {X : Type*} [Zero X] (x : ℕ → X) (j k : ℕ) : X :=
  if j ≤ k then x (k - j) else 0

@[simp] theorem zeroDelay_add {X : Type*} [Zero X] (x : ℕ → X) (j k : ℕ) :
    zeroDelay x j (k + j) = x k := by simp [zeroDelay]

/-- Zero extension preserves actual subgradient graph membership. -/
theorem zeroDelay_graph {m : ℕ} {f : (Fin m → ℝ) → EReal}
    {x g : ℕ → Fin m → ℝ} (hzero : IsSubgradientAt f 0 0)
    (hgraph : ∀ k, IsSubgradientAt f (g k) (x k)) (j k : ℕ) :
    IsSubgradientAt f (zeroDelay g j k) (zeroDelay x j k) := by
  by_cases hj : j ≤ k
  · simpa only [zeroDelay, if_pos hj] using hgraph (k - j)
  · simpa only [zeroDelay, if_neg hj] using hzero

/-- The zero-extended graph heights agree with zero extension of the heights. -/
theorem graphValue_zeroDelay {m : ℕ} (f : (Fin m → ℝ) → EReal)
    (x : ℕ → Fin m → ℝ) (j k : ℕ) :
    graphValue f (zeroDelay x j k) = zeroDelay (graphValue f ∘ x) j k := by
  by_cases hj : j ≤ k <;> simp [zeroDelay, hj, graphValue]

/-- The lag supply includes both comparison directions at their common
later time. Reindexing its reverse term yields the forward shift multiplier. -/
noncomputable def lagSupply {m : ℕ} (x g : ℕ → Fin m → ℝ)
    (a b : ℝ) (j k : ℕ) : ℝ :=
  a * dotProduct (g k) (x k - zeroDelay x j k) +
    b * dotProduct (zeroDelay g j k) (zeroDelay x j k - x k)

/-- The convex lower bound is valid also across the initial zero boundary. -/
theorem lagSupply_lower {m : ℕ} {f : (Fin m → ℝ) → EReal}
    {x g : ℕ → Fin m → ℝ} (hzero : IsSubgradientAt f 0 0)
    (hgraph : ∀ k, IsSubgradientAt f (g k) (x k))
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (j k : ℕ) :
    (a - b) * (graphValue f (x k) - zeroDelay (graphValue f ∘ x) j k) ≤
      lagSupply x g a b j k := by
  simpa only [lagSupply, graphValue_zeroDelay] using
    directed_lag_lower (hgraph k) (zeroDelay_graph hzero hgraph j k) ha hb

/-- Young's inequality controls coordinate pairings without depending on the
supremum norm instance of the coordinate function type. -/
theorem abs_dotProduct_le_square {m : ℕ} (x y : Fin m → ℝ) :
    |dotProduct x y| ≤ (coordinateSquare x + coordinateSquare y) / 2 := by
  have hp := coordinateSquare_nonneg (x + y)
  have hm := coordinateSquare_nonneg (x - y)
  simp only [coordinateSquare, add_dotProduct, sub_dotProduct, dotProduct_add,
    dotProduct_sub] at hp hm
  rw [dotProduct_comm y x] at hp hm
  apply abs_le.mpr
  constructor <;> dsimp only [coordinateSquare] <;> linarith

end ADMM.UnitCircle.Supply

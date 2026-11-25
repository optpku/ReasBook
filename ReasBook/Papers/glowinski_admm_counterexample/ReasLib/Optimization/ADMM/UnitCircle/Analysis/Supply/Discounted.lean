/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Supply.Convexity
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Continuity

@[expose] public section

open scoped BigOperators Topology
open ADMM.ConvergenceProof Filter

namespace ADMM.UnitCircle.Supply

/-- Squared time discount, with the first actual graph point indexed by zero. -/
def timeWeight (α : ℝ) (k : ℕ) : ℝ := α ^ (2 * k)

lemma timeWeight_nonneg (α : ℝ) (k : ℕ) : 0 ≤ timeWeight α k := by
  rw [timeWeight, pow_mul]
  positivity

lemma timeWeight_add (α : ℝ) (k j : ℕ) :
    timeWeight α (k + j) = timeWeight α j * timeWeight α k := by
  simp only [timeWeight, Nat.mul_add, pow_add]
  ring

/-- Reindexing a zero-extended delay preserves summability and multiplies the
weighted total by the squared lag discount. -/
theorem weighted_zeroDelay {x : ℕ → ℝ} {α : ℝ}
    (hx : Summable (fun k ↦ timeWeight α k * x k)) (j : ℕ) :
    Summable (fun k ↦ timeWeight α k * zeroDelay x j k) ∧
      (∑' k, timeWeight α k * zeroDelay x j k) =
        timeWeight α j * ∑' k, timeWeight α k * x k := by
  let f : ℕ → ℝ := fun k ↦ timeWeight α k * zeroDelay x j k
  have htail : (fun k ↦ f (k + j)) =
      fun k ↦ timeWeight α j * (timeWeight α k * x k) := by
    funext k
    simp only [f, zeroDelay_add, timeWeight_add]
    ring
  have hs : Summable f := (summable_nat_add_iff j).1 (htail ▸ hx.mul_left _)
  refine ⟨hs, ?_⟩
  have hp : ∑ k ∈ Finset.range j, f k = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hkj : ¬ j ≤ k := Nat.not_le.mpr (Finset.mem_range.mp hk)
    simp only [f, zeroDelay, if_neg hkj, mul_zero]
  have heq := hs.sum_add_tsum_nat_add j
  rw [hp, zero_add, htail, tsum_mul_left] at heq
  exact heq.symm

/-- Weighted coordinate square summability implies absolute summability of
coordinate pairings, by Young's inequality term by term. -/
theorem summable_weighted_dot {m : ℕ} {x y : ℕ → Fin m → ℝ} {α : ℝ}
    (hx : Summable (fun k ↦ timeWeight α k * coordinateSquare (x k)))
    (hy : Summable (fun k ↦ timeWeight α k * coordinateSquare (y k))) :
    Summable (fun k ↦ timeWeight α k * dotProduct (x k) (y k)) := by
  apply Summable.of_norm_bounded ((hx.add hy).div_const 2)
  intro k
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (timeWeight_nonneg α k)]
  have h := mul_le_mul_of_nonneg_left (abs_dotProduct_le_square (x k) (y k))
    (timeWeight_nonneg α k)
  nlinarith

/-- The square of a delayed coordinate sequence is the delayed square. -/
lemma coordinateSquare_zeroDelay {m : ℕ} (x : ℕ → Fin m → ℝ) (j k : ℕ) :
    coordinateSquare (zeroDelay x j k) = zeroDelay (coordinateSquare ∘ x) j k := by
  by_cases hj : j ≤ k <;> simp [zeroDelay, hj, coordinateSquare]

/-- All lag pairings in the finite supply are absolutely summable whenever
the discounted graph points and normals are square summable. -/
theorem summable_weighted_lagSupply {m : ℕ} {x g : ℕ → Fin m → ℝ} {α : ℝ}
    (hx : Summable (fun k ↦ timeWeight α k * coordinateSquare (x k)))
    (hg : Summable (fun k ↦ timeWeight α k * coordinateSquare (g k)))
    (a b : ℝ) (j : ℕ) :
    Summable (fun k ↦ timeWeight α k * lagSupply x g a b j k) := by
  have hxd : Summable (fun k ↦ timeWeight α k * coordinateSquare (zeroDelay x j k)) := by
    simpa only [coordinateSquare_zeroDelay, Function.comp_def] using
      (weighted_zeroDelay hx j).1
  have hgd : Summable (fun k ↦ timeWeight α k * coordinateSquare (zeroDelay g j k)) := by
    simpa only [coordinateSquare_zeroDelay, Function.comp_def] using
      (weighted_zeroDelay hg j).1
  have h₁ := summable_weighted_dot hg hx
  have h₂ := summable_weighted_dot hg hxd
  have h₃ := summable_weighted_dot hgd hxd
  have h₄ := summable_weighted_dot hgd hx
  apply (((h₁.sub h₂).mul_left a).add ((h₃.sub h₄).mul_left b)).congr
  intro k
  simp only [lagSupply, dotProduct_sub]
  ring

/-- Convex graph heights are absolutely summable under the same discounted
square summability, since they lie between zero and the origin pairing. -/
theorem summable_weighted_graphValue {m : ℕ} {f : (Fin m → ℝ) → EReal}
    {x g : ℕ → Fin m → ℝ} {α : ℝ} (hzero : IsSubgradientAt f 0 0)
    (hgraph : ∀ k, IsSubgradientAt f (g k) (x k))
    (hx : Summable (fun k ↦ timeWeight α k * coordinateSquare (x k)))
    (hg : Summable (fun k ↦ timeWeight α k * coordinateSquare (g k))) :
    Summable (fun k ↦ timeWeight α k * graphValue f (x k)) := by
  apply Summable.of_nonneg_of_le
    (fun k ↦ mul_nonneg (timeWeight_nonneg α k) (graphValue_bounds hzero (hgraph k)).1)
    (fun k ↦ mul_le_mul_of_nonneg_left (graphValue_bounds hzero (hgraph k)).2
      (timeWeight_nonneg α k))
    (summable_weighted_dot hg hx)

/-- The signed potential difference left by one lag after the time sum is
exactly multiplied by `1-α^(2j)`. -/
theorem weighted_lag_lower {m : ℕ} {f : (Fin m → ℝ) → EReal}
    {x g : ℕ → Fin m → ℝ} {α : ℝ} (hzero : IsSubgradientAt f 0 0)
    (hgraph : ∀ k, IsSubgradientAt f (g k) (x k))
    (hx : Summable (fun k ↦ timeWeight α k * coordinateSquare (x k)))
    (hg : Summable (fun k ↦ timeWeight α k * coordinateSquare (g k)))
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (j : ℕ) :
    (a - b) * (1 - timeWeight α j) * (∑' k, timeWeight α k * graphValue f (x k)) ≤
      ∑' k, timeWeight α k * lagSupply x g a b j k := by
  have hv := summable_weighted_graphValue hzero hgraph hx hg
  have hvd := weighted_zeroDelay hv j
  have hs : Summable (fun k ↦ timeWeight α k *
      ((a - b) * (graphValue f (x k) - zeroDelay (graphValue f ∘ x) j k))) := by
    apply ((hv.sub hvd.1).mul_left (a - b)).congr
    intro k
    simp only [Function.comp_def]
    ring
  have h := hs.tsum_le_tsum (fun k ↦ mul_le_mul_of_nonneg_left
    (lagSupply_lower hzero hgraph ha hb j k) (timeWeight_nonneg α k))
    (summable_weighted_lagSupply hx hg a b j)
  have heq : (∑' k, timeWeight α k *
      ((a - b) * (graphValue f (x k) - zeroDelay (graphValue f ∘ x) j k))) =
      (a - b) * (1 - timeWeight α j) *
        (∑' k, timeWeight α k * graphValue f (x k)) := by
    calc
      _ = (∑' k, (a - b) * (timeWeight α k * graphValue f (x k) -
          timeWeight α k * zeroDelay (graphValue f ∘ x) j k)) := by
        apply tsum_congr
        intro k
        ring
      _ = _ := by
        simp only [Function.comp_def]
        rw [tsum_mul_left, hv.tsum_sub hvd.1, hvd.2]
        ring
  rwa [heq] at h

end ADMM.UnitCircle.Supply

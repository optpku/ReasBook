/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Causal.ScaledProxGraph
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Causal.DiscountedStability
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Causal.Pairing
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Supply.LagOperatorBridge
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Initialized.WeightedSignals

@[expose] public section

open scoped BigOperators ENNReal
open ADMM.ConvergenceProof

namespace ADMM.UnitCircle.Causal

/-- Weighted summability follows from an exact discounting identity and
already established vector `ℓ₂` membership. -/
theorem squareSummable_of_discount_eq {m : ℕ} (α : ℝ)
    (v : ℕ → BlockVector m) (hv : Memℓp v 2) (b : Fin 2)
    (x : ℕ → Fin m → ℝ) (h : ∀ k, α ^ k • x k = WithLp.ofLp (v k b)) :
    Initialized.SquareSummable α x := by
  apply (block_square_summable v hv b).congr
  intro k
  rw [← h k, Initialized.coordinateSquare_smul]
  simp only [Supply.timeWeight, ← pow_mul, Nat.mul_comm k 2]

/-- The same identity gives exact equality of the scalar Fourier sequences. -/
theorem complexLp_of_discount_eq {m : ℕ} (α : ℝ)
    (v : ℕ → BlockVector m) (hv : Memℓp v 2) (b : Fin 2)
    (x : ℕ → Fin m → ℝ) (h : ∀ k, α ^ k • x k = WithLp.ofLp (v k b)) (a : Fin m) :
    Supply.complexLp α x (squareSummable_of_discount_eq α v hv b x h) a =
      coordinateLp v hv b a := by
  ext z
  cases z with
  | ofNat k =>
    change Supply.complexSequence α x a (k : ℤ) = coordinateLp v hv b a (k : ℤ)
    rw [Supply.complexSequence_nat, coordinateLp_nat]
    have hc := congrArg (fun t : Fin m → ℝ ↦ (t a : ℂ)) (h k)
    simpa only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul] using hc
  | negSucc k =>
    change Supply.complexSequence α x a (-(k + 1 : ℤ)) =
      coordinateLp v hv b a (-(k + 1 : ℤ))
    rw [Supply.complexSequence_negSucc, coordinateLp_negSucc]

theorem coordinateLp_sub {m : ℕ} (v y : ℕ → BlockVector m)
    (hv : Memℓp v 2) (hy : Memℓp y 2) (b : Fin 2) (a : Fin m) :
    coordinateLp (v - y) (hv.sub hy) b a = coordinateLp v hv b a - coordinateLp y hy b a := by
  ext z
  change coordinateLp (v - y) (hv.sub hy) b a z = coordinateLp v hv b a z - coordinateLp y hy b a z
  cases z with
  | ofNat k => simp [Complex.ofReal_sub]
  | negSucc k =>
    change coordinateLp (v - y) (hv.sub hy) b a (-(k + 1 : ℤ)) =
      coordinateLp v hv b a (-(k + 1 : ℤ)) - coordinateLp y hy b a (-(k + 1 : ℤ))
    rw [coordinateLp_negSucc, coordinateLp_negSucc, coordinateLp_negSucc, sub_self]

noncomputable def rawHomotopyInput {m : ℕ} (α : ℝ) (v : ℕ → BlockVector m)
    (b : Fin 2) (k : ℕ) : Fin m → ℝ :=
  (α ^ (k + 1))⁻¹ • WithLp.ofLp (v k b)

noncomputable def rawHomotopyPoint {m : ℕ}
    {φ : Fin 2 → (Fin m → ℝ) → EReal} (hφ : ∀ b, IsClosedProperConvex (φ b))
    (α τ : ℝ) (v : ℕ → BlockVector m) (b : Fin 2) (k : ℕ) : Fin m → ℝ :=
  α • (τ • proximalMap (hφ b) (rawHomotopyInput α v b k))

noncomputable def rawHomotopyNormal {m : ℕ}
    {φ : Fin 2 → (Fin m → ℝ) → EReal} (hφ : ∀ b, IsClosedProperConvex (φ b))
    (α τ : ℝ) (v : ℕ → BlockVector m) (b : Fin 2) (k : ℕ) : Fin m → ℝ :=
  α • (rawHomotopyInput α v b k - τ • proximalMap (hφ b) (rawHomotopyInput α v b k))

theorem rawHomotopyPoint_discount {m : ℕ}
    {φ : Fin 2 → (Fin m → ℝ) → EReal} (hφ : ∀ b, IsClosedProperConvex (φ b))
    (α τ : ℝ) (v : ℕ → BlockVector m) (b : Fin 2) (k : ℕ) :
    α ^ k • rawHomotopyPoint hφ α τ v b k =
      WithLp.ofLp ((τ • discountedProx hφ α v) k b) := by
  simp only [rawHomotopyPoint, discountedProx, discountedProxBlock, proximalMapEuclidean,
    Pi.smul_apply, WithLp.ofLp_smul, WithLp.ofLp_toLp, rawHomotopyInput, pow_succ]
  module

theorem rawHomotopyNormal_discount {m : ℕ}
    {φ : Fin 2 → (Fin m → ℝ) → EReal} (hφ : ∀ b, IsClosedProperConvex (φ b))
    {α : ℝ} (hα : 0 < α) (τ : ℝ) (v : ℕ → BlockVector m) (b : Fin 2) (k : ℕ) :
    α ^ k • rawHomotopyNormal hφ α τ v b k =
      WithLp.ofLp ((v - τ • discountedProx hφ α v) k b) := by
  have ha : α ^ (k + 1) ≠ 0 := pow_ne_zero _ hα.ne'
  simp only [rawHomotopyNormal, discountedProx, discountedProxBlock, proximalMapEuclidean,
    Pi.sub_apply, Pi.smul_apply, WithLp.ofLp_sub, WithLp.ofLp_smul, WithLp.ofLp_toLp,
    rawHomotopyInput, smul_sub, smul_smul]
  rw [← mul_assoc (α ^ k) α, ← pow_succ, mul_inv_cancel₀ ha, one_smul]
  module

/-- The actual scaled discounted proximal family has nonnegative supply,
including `τ=0`. This connects its finite convex graph data to precisely the
same bilateral lag operators used by Parseval separation. -/
theorem homotopy_pairedSupply_nonneg {m ℓ : ℕ} (c : LagWeights ℓ)
    {φ : Fin 2 → (Fin m → ℝ) → EReal} (hφ : ∀ b, IsClosedProperConvex (φ b))
    (hzero : ∀ b, IsSubgradientAt (φ b) 0 0) {α : ℝ} (hα : 0 < α)
    (τ : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (v : ℕ → BlockVector m) (hv : Memℓp v 2)
    (hcorrection : ∀ b, |Supply.discountCorrection c b α| ≤ c.omega / 2) :
    0 ≤ pairedSupply c α v (τ • discountedProx hφ α v) hv
      ((discountedProx_memℓp hφ hzero hα v hv).const_smul τ) := by
  let y := τ • discountedProx hφ α v
  have hy : Memℓp y 2 := (discountedProx_memℓp hφ hzero hα v hv).const_smul τ
  unfold pairedSupply
  apply Finset.sum_nonneg
  intro b _
  let X := rawHomotopyPoint hφ α τ v b
  let G := rawHomotopyNormal hφ α τ v b
  have hx := squareSummable_of_discount_eq α y hy b X
    (rawHomotopyPoint_discount hφ α τ v b)
  have hg := squareSummable_of_discount_eq α (v - y) (hv.sub hy) b G
    (rawHomotopyNormal_discount hφ hα τ v b)
  have hdata : Supply.GraphData X G :=
    (scaledProximalGraphData (hφ b) (hzero b) (rawHomotopyInput α v b) τ hτ0 hτ1).scale α
  have hs := Supply.discounted_supply_of_graphData c b hdata hx hg (hcorrection b)
  have hsign := hs.1.trans hs.2
  have hi := congrArg Complex.re (Supply.weighted_blockSupply_inner c b α X G hx hg)
  simp only [Complex.ofReal_re, Complex.re_sum] at hi
  rw [hi] at hsign
  convert! hsign using 1
  apply Finset.sum_congr rfl
  intro a _
  rw [complexLp_of_discount_eq α y hy b X (rawHomotopyPoint_discount hφ α τ v b),
    complexLp_of_discount_eq α (v - y) (hv.sub hy) b G
      (rawHomotopyNormal_discount hφ hα τ v b), coordinateLp_sub]

end ADMM.UnitCircle.Causal

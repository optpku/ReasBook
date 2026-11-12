/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Causal.Proximal
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Causal.Truncation

@[expose] public section

open scoped ENNReal

namespace ADMM.UnitCircle.Causal

/-- The two graph blocks, using Euclidean coordinates within each block. -/
abbrev BlockVector (m : ℕ) := Fin 2 → EuclideanSpace ℝ (Fin m)

noncomputable def proximalMapEuclidean {m : ℕ} {φ : (Fin m → ℝ) → EReal}
    (hφ : IsClosedProperConvex φ) (x : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 (proximalMap hφ (WithLp.ofLp x))

theorem proximalMapEuclidean_nonexpansive {m : ℕ} {φ : (Fin m → ℝ) → EReal}
    (hφ : IsClosedProperConvex φ) (x y : EuclideanSpace ℝ (Fin m)) :
    ‖proximalMapEuclidean hφ x - proximalMapEuclidean hφ y‖ ≤ ‖x - y‖ := by
  simpa only [proximalMapEuclidean, WithLp.toLp_sub, WithLp.ofLp_sub,
    WithLp.toLp_ofLp] using
    proximalMap_euclidean_nonexpansive hφ (WithLp.ofLp x) (WithLp.ofLp y)

@[simp] theorem proximalMapEuclidean_zero {m : ℕ} {φ : (Fin m → ℝ) → EReal}
    (hφ : IsClosedProperConvex φ) (hzero : IsSubgradientAt φ 0 0) :
    proximalMapEuclidean hφ 0 = 0 := by
  simp [proximalMapEuclidean, proximalMap_zero hφ hzero]

/-- Conjugating a proximal map by a positive time discount preserves its
nonexpansive constant. Time index zero corresponds to manuscript step one. -/
noncomputable def discountedProxBlock {m : ℕ} {φ : (Fin m → ℝ) → EReal}
    (hφ : IsClosedProperConvex φ) (α : ℝ) (k : ℕ)
    (x : EuclideanSpace ℝ (Fin m)) : EuclideanSpace ℝ (Fin m) :=
  α ^ (k + 1) • proximalMapEuclidean hφ ((α ^ (k + 1))⁻¹ • x)

theorem discountedProxBlock_nonexpansive {m : ℕ} {φ : (Fin m → ℝ) → EReal}
    (hφ : IsClosedProperConvex φ) {α : ℝ} (hα : 0 < α) (k : ℕ)
    (x y : EuclideanSpace ℝ (Fin m)) :
    ‖discountedProxBlock hφ α k x - discountedProxBlock hφ α k y‖ ≤ ‖x - y‖ := by
  have ha : α ^ (k + 1) ≠ 0 := pow_ne_zero _ hα.ne'
  simp only [discountedProxBlock, ← smul_sub, norm_smul]
  calc
    ‖α ^ (k + 1)‖ * ‖proximalMapEuclidean hφ ((α ^ (k + 1))⁻¹ • x) -
        proximalMapEuclidean hφ ((α ^ (k + 1))⁻¹ • y)‖ ≤
        ‖α ^ (k + 1)‖ * ‖(α ^ (k + 1))⁻¹ • x - (α ^ (k + 1))⁻¹ • y‖ :=
      mul_le_mul_of_nonneg_left (proximalMapEuclidean_nonexpansive hφ _ _) (norm_nonneg _)
    _ = ‖x - y‖ := by
      rw [← smul_sub, norm_smul, norm_inv, ← mul_assoc,
        mul_inv_cancel₀ (norm_ne_zero_iff.mpr ha), one_mul]

@[simp] theorem discountedProxBlock_zero {m : ℕ} {φ : (Fin m → ℝ) → EReal}
    (hφ : IsClosedProperConvex φ) (hzero : IsSubgradientAt φ 0 0) (α : ℝ) (k : ℕ) :
    discountedProxBlock hφ α k 0 = 0 := by
  simp [discountedProxBlock, proximalMapEuclidean_zero hφ hzero]

/-- The manuscript's discounted proximal operator on both one-sided blocks. -/
noncomputable def discountedProx {m : ℕ} {φ : Fin 2 → (Fin m → ℝ) → EReal}
    (hφ : ∀ b, IsClosedProperConvex (φ b)) (α : ℝ)
    (v : ℕ → BlockVector m) (k : ℕ) : BlockVector m :=
  fun b ↦ discountedProxBlock (hφ b) α k (v k b)

theorem discountedProx_pointwise_nonexpansive {m : ℕ}
    {φ : Fin 2 → (Fin m → ℝ) → EReal} (hφ : ∀ b, IsClosedProperConvex (φ b))
    {α : ℝ} (hα : 0 < α) (v w : ℕ → BlockVector m) (k : ℕ) :
    ‖discountedProx hφ α v k - discountedProx hφ α w k‖ ≤ ‖v k - w k‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro b
  exact (discountedProxBlock_nonexpansive (hφ b) hα k (v k b) (w k b)).trans
    (norm_le_pi_norm (v k - w k) b)

/-- Nonexpansiveness holds on every finite prefix, before any infinite
sequence is assumed to lie in `ℓ₂`. -/
theorem discountedProx_prefix_nonexpansive {m : ℕ}
    {φ : Fin 2 → (Fin m → ℝ) → EReal} (hφ : ∀ b, IsClosedProperConvex (φ b))
    {α : ℝ} (hα : 0 < α) (v w : ℕ → BlockVector m) (T : ℕ) :
    ‖truncate T (discountedProx hφ α v - discountedProx hφ α w)‖ ≤
      ‖truncate T (v - w)‖ := by
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro k
  by_cases hk : k < T
  · simpa only [truncate_apply, hk, if_true, Pi.sub_apply] using
      discountedProx_pointwise_nonexpansive hφ hα v w k
  · simp [hk]

@[simp] theorem discountedProx_zero {m : ℕ}
    {φ : Fin 2 → (Fin m → ℝ) → EReal} (hφ : ∀ b, IsClosedProperConvex (φ b))
    (hzero : ∀ b, IsSubgradientAt (φ b) 0 0) (α : ℝ) :
    discountedProx hφ α 0 = 0 := by
  funext k b
  simp [discountedProx, discountedProxBlock_zero (hφ b) (hzero b)]

/-- The zero-fixing finite-prefix norm estimate needed by the causal homotopy. -/
theorem discountedProx_prefix_norm_le {m : ℕ}
    {φ : Fin 2 → (Fin m → ℝ) → EReal} (hφ : ∀ b, IsClosedProperConvex (φ b))
    (hzero : ∀ b, IsSubgradientAt (φ b) 0 0) {α : ℝ} (hα : 0 < α)
    (v : ℕ → BlockVector m) (T : ℕ) :
    ‖truncate T (discountedProx hφ α v)‖ ≤ ‖truncate T v‖ := by
  simpa only [discountedProx_zero hφ hzero α, sub_zero] using
    discountedProx_prefix_nonexpansive hφ hα v 0 T

end ADMM.UnitCircle.Causal

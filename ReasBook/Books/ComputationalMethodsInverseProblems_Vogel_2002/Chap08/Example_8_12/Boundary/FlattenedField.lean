/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.InnerProductSpace.PiL2
public section
noncomputable section
open scoped BigOperators
namespace VariationalRegularization
namespace GraphFlattening

lemma clm_apply_eq_sum_single {n : ℕ}
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    B v = ∑ j : Fin n, v j * B (EuclideanSpace.single j 1) := by
  have hv : v = ∑ j : Fin n, v j • EuclideanSpace.single j (1 : ℝ) := by
    apply PiLp.ext
    intro j
    simp [EuclideanSpace.single, Pi.single_apply]
  conv_lhs => rw [hv, map_sum]
  simp only [map_smul, smul_eq_mul]

/-- The signed graph shear. -/
@[expose] def chart {n : ℕ} (ψ : EuclideanSpace ℝ (Fin n) → ℝ) (σ : ℝ)
    (q : EuclideanSpace ℝ (Fin n) × ℝ) := (q.1, ψ q.1 + σ * q.2)

/-- The Piola transform in product coordinates. -/
@[expose] def field {n : ℕ} (ψ : EuclideanSpace ℝ (Fin n) → ℝ) (σ : ℝ)
    (G : EuclideanSpace ℝ (Fin n) × ℝ → EuclideanSpace ℝ (Fin n) × ℝ)
    (q : EuclideanSpace ℝ (Fin n) × ℝ) :=
  let v := G (chart ψ σ q)
  (v.1, σ * (v.2 - fderiv ℝ ψ q.1 v.1))

/-- A `C²` graph and `C¹` original field give a `C¹` Piola field. -/
lemma contDiffAt_field {n : ℕ} {ψ : EuclideanSpace ℝ (Fin n) → ℝ} {σ : ℝ}
    {G : EuclideanSpace ℝ (Fin n) × ℝ → EuclideanSpace ℝ (Fin n) × ℝ}
    {q : EuclideanSpace ℝ (Fin n) × ℝ}
    (hψ : ContDiffAt ℝ 2 ψ q.1) (hG : ContDiffAt ℝ 1 G (chart ψ σ q)) :
    ContDiffAt ℝ 1 (field ψ σ G) q := by
  have hchart : ContDiffAt ℝ 1 (chart ψ σ) q :=
    contDiffAt_fst.prodMk (((hψ.of_le (m := 1) (by norm_num)).comp q contDiffAt_fst).add
      (contDiffAt_const.mul contDiffAt_snd))
  have hcomp := hG.comp q hchart
  have hB := (hψ.fderiv_right (m := 1) (by norm_num)).comp q contDiffAt_fst
  exact hcomp.fst.prodMk (contDiffAt_const.mul (hcomp.snd.sub (hB.clm_apply hcomp.fst)))

lemma divergence_eq {n : ℕ} {ψ : EuclideanSpace ℝ (Fin n) → ℝ} {σ : ℝ}
    {G : EuclideanSpace ℝ (Fin n) × ℝ → EuclideanSpace ℝ (Fin n) × ℝ}
    {q : EuclideanSpace ℝ (Fin n) × ℝ}
    (hψ : ContDiffAt ℝ 2 ψ q.1) (hσ : σ * σ = 1)
    (hG : DifferentiableAt ℝ G (chart ψ σ q)) :
    (∑ j : Fin n, (fderiv ℝ (field ψ σ G) q (EuclideanSpace.single j 1, 0)).1 j) +
        (fderiv ℝ (field ψ σ G) q (0, 1)).2 =
      (∑ j : Fin n, (fderiv ℝ G (chart ψ σ q) (EuclideanSpace.single j 1, 0)).1 j) +
        (fderiv ℝ G (chart ψ σ q) (0, 1)).2 := by
  let A := fderiv ℝ G (chart ψ σ q)
  let B := fderiv ℝ ψ q.1
  let C := fderiv ℝ (fderiv ℝ ψ) q.1
  let L : (EuclideanSpace ℝ (Fin n) × ℝ) →L[ℝ] (EuclideanSpace ℝ (Fin n) × ℝ) :=
    (ContinuousLinearMap.fst ℝ _ _).prod
      (B.comp (ContinuousLinearMap.fst ℝ _ _) + σ • ContinuousLinearMap.snd ℝ _ _)
  have hchart : HasFDerivAt (chart ψ σ) L q := by
    exact hasFDerivAt_fst.prodMk
      (((hψ.differentiableAt (by norm_num)).hasFDerivAt.comp q hasFDerivAt_fst).add
        (hasFDerivAt_snd.const_mul σ))
  have hcomp := hG.hasFDerivAt.comp q hchart
  have hB : HasFDerivAt (fun p : EuclideanSpace ℝ (Fin n) × ℝ ↦ fderiv ℝ ψ p.1)
      (C.comp (ContinuousLinearMap.fst ℝ _ _)) q :=
    ((hψ.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt.comp q hasFDerivAt_fst
  have hF := hcomp.fst.prodMk ((hcomp.snd.sub (hB.clm_apply hcomp.fst)).const_mul σ)
  have hfd := hF.fderiv
  change fderiv ℝ (field ψ σ G) q = _ at hfd
  rw [hfd]
  have hsum : B ((A (0, 1)).1) =
      ∑ j : Fin n, (A (0, 1)).1 j * B (EuclideanSpace.single j 1) := by
    have hv : (A (0, 1)).1 =
        ∑ j : Fin n, (A (0, 1)).1 j • EuclideanSpace.single j (1 : ℝ) := by
      apply PiLp.ext
      intro j
      simp [EuclideanSpace.single, Pi.single_apply]
    conv_lhs => rw [hv, map_sum]
    simp only [map_smul, smul_eq_mul]
  change (∑ j : Fin n, (A (L (EuclideanSpace.single j 1, 0))).1 j) +
      σ * ((A (L (0, 1))).2 -
        (B (A (L (0, 1))).1 + C 0 (G (chart ψ σ q)).1)) = _
  simp only [L, ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
    add_apply, smul_apply, map_zero, zero_apply, add_zero, smul_eq_mul]
  change (∑ j : Fin n, (A (EuclideanSpace.single j 1,
      B (EuclideanSpace.single j 1) + σ * 0)).1 j) +
      σ * ((A (0, B 0 + σ * 1)).2 - B (A (0, B 0 + σ * 1)).1) = _
  simp only [map_zero, mul_zero, add_zero, zero_add, mul_one]
  have hA (j : Fin n) : A (EuclideanSpace.single j 1, B (EuclideanSpace.single j 1)) =
      A (EuclideanSpace.single j 1, 0) + B (EuclideanSpace.single j 1) • A (0, 1) := by
    rw [← map_smul, ← map_add]
    congr 1
    apply Prod.ext <;> simp
  simp only [hA, Prod.fst_add, PiLp.add_apply]
  rw [Finset.sum_add_distrib]
  have hvert : A (0, σ) = σ • A (0, 1) := by
    rw [← map_smul]
    congr 1
    apply Prod.ext <;> simp
  rw [hvert]
  change (∑ j : Fin n, (A (EuclideanSpace.single j 1, 0)).1 j) +
      (∑ j : Fin n, B (EuclideanSpace.single j 1) * (A (0, 1)).1 j) +
      σ * (σ * (A (0, 1)).2 - B (σ • (A (0, 1)).1)) =
      (∑ j : Fin n, (A (EuclideanSpace.single j 1, 0)).1 j) + (A (0, 1)).2
  rw [map_smul, smul_eq_mul, hsum]
  have hcancel : (∑ j : Fin n, B (EuclideanSpace.single j 1) * (A (0, 1)).1 j) =
      ∑ j : Fin n, (A (0, 1)).1 j * B (EuclideanSpace.single j 1) := by
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  rw [hcancel]
  rw [mul_sub, ← mul_assoc σ σ _, ← mul_assoc σ σ _, hσ]
  ring
end GraphFlattening
end VariationalRegularization

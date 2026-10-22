/-
Authors: Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Papers/SmoothMinimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib
import SmoothMinimization_Nesterov_2004.section05_part4

open scoped BigOperators

/-- Lemma 1.5.3.1.
Let the sequence `{α_k}` satisfy condition (3.6) and suppose that relation `(R_k)` holds for some
`k ≥ 0`. Choose `γ_k = (σ / L) α_{k+1}` and define
`x_{k+1} = τ_k z_k + (1-τ_k) y_k`, `\hat x_{k+1} = V_Q(z_k, γ_k ∇ f(x_{k+1}))`,
`y_{k+1} = τ_k \hat x_{k+1} + (1-τ_k) y_k` (equation (5.5)). Then `(R_{k+1})` holds. -/
theorem Rk_succ_update_modified {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {Q : Set E} {f d : E → ℝ} {L σ : ℝ} (α : ℕ → ℝ)
    (hQ_convex : Convex ℝ Q) (hf_convex : ConvexOn ℝ Q f)
    (hf_diff : ∀ x ∈ Q, DifferentiableAt ℝ f x)
    (hd_diff : ∀ x ∈ Q, DifferentiableAt ℝ d x)
    (hconv : StrongConvexOn Q σ d) (hσ : 0 < σ) (hL : 0 < L)
    (xSeq ySeq : ℕ → Q) (k : ℕ) (hα_pos : ∀ k, 0 < α k)
    (hα_sq : ∀ k, (α (k + 1)) ^ 2 ≤ A_k α (k + 1))
    (hRk : R_k Q f d L σ α xSeq ySeq k)
    (hzk_bregman :
      ∀ x ∈ Q,
        (L / σ) * bregmanDistance d (z_k Q f d L σ α xSeq k : E) x +
            psi_k Q f d L σ α xSeq k ≤
          (L / σ) * d x +
            Finset.sum (Finset.range (k + 1)) (fun i =>
              α i * (f (xSeq i) +
                DualPairing ((fderiv ℝ f (xSeq i)).toLinearMap) (x - xSeq i))))
    (hVQ_min :
      IsMinOn
        (fun x : E =>
          (L / σ) * bregmanDistance d (z_k Q f d L σ α xSeq k : E) x +
            α (k + 1) *
              DualPairing ((fderiv ℝ f (xSeq (k + 1))).toLinearMap)
                (x - (z_k Q f d L σ α xSeq k : E)))
        Q
        (V_Q Q d (z_k Q f d L σ α xSeq k)
          (((σ / L) * α (k + 1)) • fderiv ℝ f (xSeq (k + 1))) : E))
    (hfy_bound :
      let xk1 : E := xSeq (k + 1)
      let g : Module.Dual ℝ E := (fderiv ℝ f (xSeq (k + 1))).toLinearMap
      let γk : ℝ := (σ / L) * α (k + 1)
      let xhat : E :=
        V_Q Q d (z_k Q f d L σ α xSeq k) (γk • fderiv ℝ f (xSeq (k + 1)))
      A_k α (k + 1) * f (ySeq (k + 1)) ≤
        A_k α (k + 1) * f xk1 + α (k + 1) * DualPairing g (xhat - (z_k Q f d L σ α xSeq k : E)))
    (hx_update :
      (xSeq (k + 1) : E) =
        (α (k + 1) / A_k α (k + 1)) • (z_k Q f d L σ α xSeq k : E) +
          (1 - α (k + 1) / A_k α (k + 1)) • (ySeq k : E)) :
    R_k Q f d L σ α xSeq ySeq (k + 1) := by
  classical
  let A : ℝ := A_k α (k + 1)
  let τ : ℝ := α (k + 1) / A
  have hτ_props : 0 < A ∧ 0 ≤ τ ∧ τ ≤ 1 ∧ τ ^ 2 ≤ 1 / A := by
    simpa [A, τ] using (section03_tau_props (α := α) k hα_pos hα_sq)
  rcases hτ_props with ⟨hA_pos, hτ_nonneg, hτ_le, hτ_sq⟩
  have hA_nonneg : 0 ≤ A := le_of_lt hA_pos
  have hA_ne : (A : ℝ) ≠ 0 := ne_of_gt hA_pos
  let xk1 : E := xSeq (k + 1)
  let zk : E := z_k Q f d L σ α xSeq k
  let g : Module.Dual ℝ E := (fderiv ℝ f (xSeq (k + 1))).toLinearMap
  let γk : ℝ := (σ / L) * α (k + 1)
  let xhat : E :=
    V_Q Q d (z_k Q f d L σ α xSeq k) (γk • fderiv ℝ f (xSeq (k + 1)))
  have hpsi_linear :
      A_k α k * (f xk1 + DualPairing g ((ySeq k : E) - xk1)) ≤
        psi_k Q f d L σ α xSeq k := by
    simpa [xk1, g] using
      (section05_modified_Rk_support_at_xk1 (α := α) (xSeq := xSeq) (ySeq := ySeq) (k := k)
        (hQ_convex := hQ_convex) (hf_convex := hf_convex) (hf_diff := hf_diff)
        (hα_pos := hα_pos) (hRk := hRk))
  have hpoint :
      ∀ z ∈ Q,
        A * f (ySeq (k + 1)) ≤
          (L / σ) * d z +
            Finset.sum (Finset.range (k + 2)) (fun i =>
              α i * (f (xSeq i) +
                DualPairing ((fderiv ℝ f (xSeq i)).toLinearMap) (z - xSeq i))) := by
    intro z hz
    have hfy :
        A * f (ySeq (k + 1)) ≤ A * f xk1 + α (k + 1) * DualPairing g (xhat - zk) := by
      simpa [A, xk1, g, xhat, γk] using hfy_bound
    have hbreg_nonneg : 0 ≤ bregmanDistance d zk xhat := by
      have hzkmem : (z_k Q f d L σ α xSeq k : E) ∈ Q :=
        (z_k Q f d L σ α xSeq k).property
      have hxhatmem :
          (V_Q Q d (z_k Q f d L σ α xSeq k) (γk • fderiv ℝ f (xSeq (k + 1))) : E) ∈ Q :=
        (V_Q Q d (z_k Q f d L σ α xSeq k) (γk • fderiv ℝ f (xSeq (k + 1)))).property
      have hlower :=
        bregmanDistance_lower_bound (Q := Q) (d := d) (σ := σ) hd_diff hconv
          (z_k Q f d L σ α xSeq k : E) hzkmem xhat hxhatmem
      have hnonneg :
          0 ≤ (1 / 2 : ℝ) * σ * ‖xhat - zk‖ ^ (2 : ℕ) := by
        have hhalf_nonneg : 0 ≤ (1 / 2 : ℝ) := by norm_num
        have hσ_nonneg : 0 ≤ σ := le_of_lt hσ
        have hnorm_nonneg : 0 ≤ ‖xhat - zk‖ ^ (2 : ℕ) := by
          simp
        exact mul_nonneg (mul_nonneg hhalf_nonneg hσ_nonneg) hnorm_nonneg
      exact le_trans hnonneg hlower
    have hLσ_nonneg : 0 ≤ L / σ := by
      exact div_nonneg (le_of_lt hL) (le_of_lt hσ)
    have hB_nonneg : 0 ≤ (L / σ) * bregmanDistance d zk xhat := by
      exact mul_nonneg hLσ_nonneg hbreg_nonneg
    have hadd :
        A * f xk1 + α (k + 1) * DualPairing g (xhat - zk) ≤
          (L / σ) * bregmanDistance d zk xhat +
            A * f xk1 + α (k + 1) * DualPairing g (xhat - zk) := by
      linarith [hB_nonneg]
    have hVQ_min' :
        (L / σ) * bregmanDistance d zk xhat +
            α (k + 1) * DualPairing g (xhat - zk) ≤
          (L / σ) * bregmanDistance d zk z +
            α (k + 1) * DualPairing g (z - zk) := by
      simpa [zk, g, γk, xhat] using
        (section05_VQ_scaled_min_property (α := α) (xSeq := xSeq) (k := k) (g := g)
          (hVQ_min := hVQ_min) z hz)
    have hVQ_min'' :
        (L / σ) * bregmanDistance d zk xhat +
              A * f xk1 + α (k + 1) * DualPairing g (xhat - zk) ≤
            (L / σ) * bregmanDistance d zk z +
              A * f xk1 + α (k + 1) * DualPairing g (z - zk) := by
      have h := add_le_add_left hVQ_min' (A * f xk1)
      simpa [add_comm, add_left_comm, add_assoc] using h
    have hcombine :
        A_k α k * DualPairing g ((ySeq k : E) - xk1) +
            α (k + 1) * DualPairing g (z - xk1) =
          α (k + 1) * DualPairing g (z - zk) := by
      simpa [xk1, zk] using
        (section05_modified_dualpairing_combine (α := α) (xSeq := xSeq) (ySeq := ySeq) (k := k)
          (hA_pos := hA_pos) (hx_update := hx_update) g z)
    have hA_sum : A = A_k α k + α (k + 1) := by
      simp [A, A_k, Finset.sum_range_succ, add_comm, add_left_comm, add_assoc]
    have hpsi_plus :
        A_k α k * (f xk1 + DualPairing g ((ySeq k : E) - xk1)) +
            α (k + 1) * (f xk1 + DualPairing g (z - xk1)) ≤
          psi_k Q f d L σ α xSeq k +
            α (k + 1) * (f xk1 + DualPairing g (z - xk1)) := by
      have h :=
        add_le_add_right hpsi_linear
          (α (k + 1) * (f xk1 + DualPairing g (z - xk1)))
      simpa [add_comm, add_left_comm, add_assoc] using h
    have hpsi_plus' :
        A * f xk1 + α (k + 1) * DualPairing g (z - zk) ≤
          psi_k Q f d L σ α xSeq k +
            α (k + 1) * (f xk1 + DualPairing g (z - xk1)) := by
      calc
        A * f xk1 + α (k + 1) * DualPairing g (z - zk) =
            (A_k α k + α (k + 1)) * f xk1 + α (k + 1) * DualPairing g (z - zk) := by
          simp [hA_sum]
        _ =
            A_k α k * f xk1 + α (k + 1) * f xk1 + α (k + 1) * DualPairing g (z - zk) := by
          ring
        _ =
            A_k α k * f xk1 + α (k + 1) * f xk1 +
              (A_k α k * DualPairing g ((ySeq k : E) - xk1) +
                α (k + 1) * DualPairing g (z - xk1)) := by
          rw [← hcombine]
        _ =
            A_k α k * (f xk1 + DualPairing g ((ySeq k : E) - xk1)) +
              α (k + 1) * (f xk1 + DualPairing g (z - xk1)) := by
          ring
        _ ≤
            psi_k Q f d L σ α xSeq k +
              α (k + 1) * (f xk1 + DualPairing g (z - xk1)) := hpsi_plus
    have hpsi_plus'' :
        (L / σ) * bregmanDistance d zk z +
              A * f xk1 + α (k + 1) * DualPairing g (z - zk) ≤
            (L / σ) * bregmanDistance d zk z +
              psi_k Q f d L σ α xSeq k +
                α (k + 1) * (f xk1 + DualPairing g (z - xk1)) := by
      have h := add_le_add_left hpsi_plus' ((L / σ) * bregmanDistance d zk z)
      simpa [add_comm, add_left_comm, add_assoc] using h
    let term : ℕ → ℝ := fun i =>
      α i * (f (xSeq i) +
        DualPairing ((fderiv ℝ f (xSeq i)).toLinearMap) (z - xSeq i))
    have hFk1_lower :
        (L / σ) * bregmanDistance d zk z +
              psi_k Q f d L σ α xSeq k +
                α (k + 1) * (f xk1 + DualPairing g (z - xk1)) ≤
            (L / σ) * d z +
              Finset.sum (Finset.range (k + 2)) term := by
      have h := hzk_bregman z hz
      have h' :=
        add_le_add_right h (α (k + 1) * (f xk1 + DualPairing g (z - xk1)))
      have hterm :
          term (k + 1) = α (k + 1) * (f xk1 + DualPairing g (z - xk1)) := by
        simp [term, xk1, g]
      have h'' :
          (L / σ) * bregmanDistance d zk z +
                psi_k Q f d L σ α xSeq k +
                  α (k + 1) * (f xk1 + DualPairing g (z - xk1)) ≤
              (L / σ) * d z + Finset.sum (Finset.range (k + 1)) term + term (k + 1) := by
        simpa [hterm, add_assoc, add_left_comm, add_comm] using h'
      simpa [term, Finset.sum_range_succ, add_assoc] using h''
    have hfinal :
        A * f (ySeq (k + 1)) ≤
          (L / σ) * d z + Finset.sum (Finset.range (k + 2)) term := by
      exact
        le_trans hfy
          (le_trans hadd (le_trans hVQ_min'' (le_trans hpsi_plus'' hFk1_lower)))
    simpa [term] using hfinal
  unfold R_k
  have hgoal :
      A_k α (k + 1) * f ↑(ySeq (k + 1)) ≤
        sInf
          ((fun a ↦
              L / σ * d a +
                ∑ x ∈ Finset.range (k + 1 + 1),
                  α x * (f ↑(xSeq x) + DualPairing (↑(fderiv ℝ f ↑(xSeq x))) (a - ↑(xSeq x)))) '' Q) := by
    refine le_csInf ?_ ?_
    · refine ⟨(L / σ) * d (xSeq (k + 1)) +
        Finset.sum (Finset.range (k + 2)) (fun i =>
          α i * (f (xSeq i) +
            DualPairing ((fderiv ℝ f (xSeq i)).toLinearMap) ((xSeq (k + 1) : E) - xSeq i))), ?_⟩
      exact ⟨(xSeq (k + 1) : E), (xSeq (k + 1)).property, rfl⟩
    · intro b hb
      rcases hb with ⟨z, hz, rfl⟩
      simpa [A] using hpoint z hz
  simpa [psi_k] using hgoal

/-- Algorithm 1.5.3.1.
Choose an initial point
`y_0 = z_0 = argmin_{x ∈ Q} { (L/σ) d(x) + (1/2) [ f(x_0) + ⟪∇ f(x_0), x - x_0⟫ ] }`
(equation (5.6_init)). For `k ≥ 0`, iterate:
(a) `z_k = argmin_{x ∈ Q} { (L/σ) d(x) + ∑_{i=0}^k (i+1)/2 [ f(x_i) + ⟪∇ f(x_i), x - x_i⟫ ] }`;
(b) `τ_k = 2/(k+3)`, `x_{k+1} = τ_k z_k + (1-τ_k) y_k`;
(c) `\hat x_{k+1} = V_Q(z_k, (σ/L) τ_k ∇ f(x_{k+1}))`;
(d) `y_{k+1} = τ_k \hat x_{k+1} + (1-τ_k) y_k` (equation (5.6)). -/
def ModifiedOptimalSchemeAlgorithm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (Q : Set E) (f d : E → ℝ) (L σ : ℝ)
    (xSeq ySeq zSeq xhatSeq : ℕ → Q) : Prop :=
  ySeq 0 = zSeq 0 ∧
  (∀ k, zSeq k = z_k Q f d L σ (fun i => ((i : ℝ) + 1) / 2) xSeq k) ∧
  (∀ k, (xSeq (k + 1) : E) =
    (2 / ((k : ℝ) + 3)) • (zSeq k : E) +
      (1 - 2 / ((k : ℝ) + 3)) • (ySeq k : E)) ∧
  (∀ k, xhatSeq (k + 1) =
    V_Q Q d (zSeq k)
      (((σ / L) * (2 / ((k : ℝ) + 3))) • fderiv ℝ f (xSeq (k + 1)))) ∧
  (∀ k, (ySeq (k + 1) : E) =
    (2 / ((k : ℝ) + 3)) • (xhatSeq (k + 1) : E) +
      (1 - 2 / ((k : ℝ) + 3)) • (ySeq k : E))

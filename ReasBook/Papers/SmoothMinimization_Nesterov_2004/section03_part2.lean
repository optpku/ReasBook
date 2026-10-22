/-
Authors: Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Papers/SmoothMinimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib
import Papers.SmoothMinimization_Nesterov_2004.section03_part1

/-- Adding a convex function preserves strong convexity. -/
lemma section03_strongConvex_add_convex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Q : Set E} {m : ℝ} {f g : E → ℝ} (hf : StrongConvexOn Q m f) (hg : ConvexOn ℝ Q g) :
    StrongConvexOn Q m (f + g) := by
  have hf' : UniformConvexOn Q (fun r => m / 2 * r ^ 2) f := hf
  have hg' : UniformConvexOn Q 0 g := hg.uniformConvexOn_zero
  have hsum : UniformConvexOn Q (fun r => m / 2 * r ^ 2 + 0) (f + g) := hf'.add hg'
  simpa [StrongConvexOn] using hsum

/-- Convexity of the affine sum term in `F_k`. -/
lemma section03_Fk_sum_convex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {Q : Set E} (hQ_convex : Convex ℝ Q) {f : E → ℝ} (α : ℕ → ℝ)
    (xSeq : ℕ → Q) (k : ℕ) (hα_pos : ∀ k, 0 < α k) :
    ConvexOn ℝ Q (fun x =>
      Finset.sum (Finset.range (k + 1)) (fun i =>
        α i * (f (xSeq i) +
          DualPairing ((fderiv ℝ f (xSeq i)).toLinearMap) (x - xSeq i)))) := by
  classical
  let term : ℕ → E → ℝ := fun i x =>
    α i * (f (xSeq i) +
      DualPairing ((fderiv ℝ f (xSeq i)).toLinearMap) (x - xSeq i))
  have hterm_convex : ∀ i, ConvexOn ℝ Q (term i) := by
    intro i
    let s : Module.Dual ℝ E := (fderiv ℝ f (xSeq i)).toLinearMap
    have hconst : ConvexOn ℝ Q (fun _ : E => f (xSeq i)) := convexOn_const _ hQ_convex
    have hlin : ConvexOn ℝ Q (fun x => DualPairing s (x - (xSeq i : E))) :=
      section03_convex_dualpairing_sub (hQ_convex := hQ_convex) s (xSeq i)
    have hadd : ConvexOn ℝ Q (fun x => f (xSeq i) + DualPairing s (x - (xSeq i : E))) := by
      simpa [add_comm, add_left_comm, add_assoc] using hconst.add hlin
    have hα_nonneg : 0 ≤ α i := le_of_lt (hα_pos i)
    simpa [term, smul_eq_mul] using (hadd.smul hα_nonneg)
  refine Finset.induction_on (Finset.range (k + 1)) ?_ ?_
  · simpa [term] using (convexOn_const (c := (0 : ℝ)) hQ_convex)
  · intro i s his hconv
    have hsum := hconv.add (hterm_convex i)
    simpa [term, Finset.sum_insert his, add_comm, add_left_comm, add_assoc] using hsum

/-- Quadratic lower bound at a minimizer of `F_k`. -/
lemma section03_Fk_quadratic_lower_bound_at_zk {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {Q : Set E} {f d : E → ℝ} {L σ : ℝ}
    (α : ℕ → ℝ) (xSeq : ℕ → Q) (k : ℕ) (hQ_convex : Convex ℝ Q)
    (hconv : StrongConvexOn Q σ d) (hσ : 0 < σ) (hL : 0 < L) (hα_pos : ∀ k, 0 < α k)
    (hzk_min :
      IsMinOn
        (fun x : E =>
          (L / σ) * d x +
            Finset.sum (Finset.range (k + 1)) (fun i =>
              α i * (f (xSeq i) +
                DualPairing ((fderiv ℝ f (xSeq i)).toLinearMap) (x - xSeq i))))
        Q (z_k Q f d L σ α xSeq k : E)) :
    ∀ x ∈ Q,
      psi_k Q f d L σ α xSeq k + (L / 2) * ‖x - (z_k Q f d L σ α xSeq k : E)‖ ^ 2 ≤
        (L / σ) * d x +
          Finset.sum (Finset.range (k + 1)) (fun i =>
            α i * (f (xSeq i) +
              DualPairing ((fderiv ℝ f (xSeq i)).toLinearMap) (x - xSeq i))) := by
  classical
  let Fk : E → ℝ := fun x =>
    (L / σ) * d x +
      Finset.sum (Finset.range (k + 1)) (fun i =>
        α i * (f (xSeq i) +
          DualPairing ((fderiv ℝ f (xSeq i)).toLinearMap) (x - xSeq i)))
  have hscaled : StrongConvexOn Q L (fun x => (L / σ) * d x) := by
    refine ⟨hconv.1, ?_⟩
    intro x hx y hy a b ha hb hab
    have hconv_d := hconv.2 hx hy ha hb hab
    have hLσ_nonneg : 0 ≤ L / σ := by
      exact div_nonneg (le_of_lt hL) (le_of_lt hσ)
    have hscaled := mul_le_mul_of_nonneg_left hconv_d hLσ_nonneg
    have hσ_ne : (σ : ℝ) ≠ 0 := ne_of_gt hσ
    calc
      (L / σ) * d (a • x + b • y) ≤
          (L / σ) * (a * d x + b * d y - a * b * ((σ / 2) * ‖x - y‖ ^ (2 : ℕ))) := hscaled
      _ = a * ((L / σ) * d x) + b * ((L / σ) * d y) -
            a * b * ((L / 2) * ‖x - y‖ ^ (2 : ℕ)) := by
          field_simp [hσ_ne, mul_comm, mul_left_comm, mul_assoc, sub_eq_add_neg, add_comm,
            add_left_comm, add_assoc]
  have hsum_convex :
      ConvexOn ℝ Q (fun x =>
        Finset.sum (Finset.range (k + 1)) (fun i =>
          α i * (f (xSeq i) +
            DualPairing ((fderiv ℝ f (xSeq i)).toLinearMap) (x - xSeq i)))) :=
    section03_Fk_sum_convex (hQ_convex := hQ_convex) (α := α) (xSeq := xSeq) (k := k)
      (hα_pos := hα_pos)
  have hFk_strong : StrongConvexOn Q L Fk := by
    have hsum_uniform : UniformConvexOn Q 0 (fun x =>
      Finset.sum (Finset.range (k + 1)) (fun i =>
        α i * (f (xSeq i) +
          DualPairing ((fderiv ℝ f (xSeq i)).toLinearMap) (x - xSeq i)))) :=
      hsum_convex.uniformConvexOn_zero
    have hscaled' : UniformConvexOn Q (fun r => L / 2 * r ^ 2) (fun x => (L / σ) * d x) :=
      hscaled
    have hsum :
        UniformConvexOn Q (fun r => L / 2 * r ^ 2 + 0) (fun x => (L / σ) * d x +
          Finset.sum (Finset.range (k + 1)) (fun i =>
            α i * (f (xSeq i) +
              DualPairing ((fderiv ℝ f (xSeq i)).toLinearMap) (x - xSeq i)))) :=
      hscaled'.add hsum_uniform
    simpa [Fk, StrongConvexOn] using hsum
  intro x hx
  have hzk_mem : (z_k Q f d L σ α xSeq k : E) ∈ Q := (z_k Q f d L σ α xSeq k).property
  have hlower :
      Fk (z_k Q f d L σ α xSeq k : E) +
          (L / 2) * ‖x - (z_k Q f d L σ α xSeq k : E)‖ ^ (2 : ℕ) ≤
        Fk x := by
    exact
      strongConvexOn_lower_quadratic_of_isMinOn Q Fk L
        (z_k Q f d L σ α xSeq k) hFk_strong hzk_mem hzk_min x hx
  have hBdd : BddBelow (Fk '' Q) := by
    refine ⟨Fk (z_k Q f d L σ α xSeq k : E), ?_⟩
    intro b hb
    rcases hb with ⟨z, hz, rfl⟩
    have hmin := (isMinOn_iff.mp hzk_min) z hz
    simpa [Fk] using hmin
  have hpsi_le : psi_k Q f d L σ α xSeq k ≤ Fk (z_k Q f d L σ α xSeq k : E) := by
    refine csInf_le hBdd ?_
    exact ⟨(z_k Q f d L σ α xSeq k : E), hzk_mem, rfl⟩
  have hpsi_le' :
      psi_k Q f d L σ α xSeq k + (L / 2) * ‖x - (z_k Q f d L σ α xSeq k : E)‖ ^ 2 ≤
        Fk (z_k Q f d L σ α xSeq k : E) +
          (L / 2) * ‖x - (z_k Q f d L σ α xSeq k : E)‖ ^ 2 := by
    simpa [add_comm, add_left_comm, add_assoc] using
      (add_le_add_right hpsi_le ((L / 2) * ‖x - (z_k Q f d L σ α xSeq k : E)‖ ^ 2))
  have hfinal := le_trans hpsi_le' hlower
  simpa [Fk, pow_two] using hfinal

/-- Lemma 1.3.1.
Let `{α_k}_{k≥0}` be positive numbers with `α_0 ∈ (0,1]` and `α_{k+1}^2 ≤ A_{k+1}` for all
`k ≥ 0`, where `A_{k+1} = ∑_{i=0}^{k+1} α_i` (equation (3.6)). Assume `(R_k)` holds for some
`k ≥ 0`. Define `τ_k = α_{k+1} / A_{k+1}` (equation (tau_def)) and update
`x_{k+1} = τ_k z_k + (1-τ_k) y_k`, `y_{k+1} = T_Q(x_{k+1})` (equation (3.7)).
Then `(R_{k+1})` holds. -/
theorem Rk_succ_update {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {Q : Set E} {f d : E → ℝ} {L σ : ℝ} (α : ℕ → ℝ)
    (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q) (hf_convex : ConvexOn ℝ Q f)
    (hf_diff : ∀ x ∈ Q, DifferentiableAt ℝ f x) (hL : 0 < L)
    (hgrad_lipschitz :
      ∀ x ∈ Q, ∀ y ∈ Q,
        DualNormDef ((fderiv ℝ f x).toLinearMap - (fderiv ℝ f y).toLinearMap) ≤
          L * ‖x - y‖)
    (hconv : StrongConvexOn Q σ d) (hσ : 0 < σ)
    (xSeq ySeq : ℕ → Q) (k : ℕ) (hα_pos : ∀ k, 0 < α k)
    (hα_sq : ∀ k, (α (k + 1)) ^ 2 ≤ A_k α (k + 1))
    (hRk : R_k Q f d L σ α xSeq ySeq k)
    (hzk_min :
      IsMinOn
        (fun x : E =>
          (L / σ) * d x +
            Finset.sum (Finset.range (k + 1)) (fun i =>
              α i * (f (xSeq i) +
                DualPairing ((fderiv ℝ f (xSeq i)).toLinearMap) (x - xSeq i))))
        Q (z_k Q f d L σ α xSeq k : E))
    (hx_update :
      (xSeq (k + 1) : E) =
        (α (k + 1) / A_k α (k + 1)) • (z_k Q f d L σ α xSeq k : E) +
          (1 - α (k + 1) / A_k α (k + 1)) • (ySeq k : E))
    (hy_update : ySeq (k + 1) = T_Q Q f L (xSeq (k + 1))) :
    R_k Q f d L σ α xSeq ySeq (k + 1) := by
  classical
  let A := A_k α (k + 1)
  let τ := α (k + 1) / A
  have hτ_props : 0 < A ∧ 0 ≤ τ ∧ τ ≤ 1 ∧ τ ^ 2 ≤ 1 / A := by
    simpa [A, τ] using (section03_tau_props (α := α) k hα_pos hα_sq)
  rcases hτ_props with ⟨hA_pos, hτ_nonneg, hτ_le, hτ_sq⟩
  have hA_nonneg : 0 ≤ A := le_of_lt hA_pos
  have hA_ne : (A : ℝ) ≠ 0 := ne_of_gt hA_pos
  let xk1 : E := xSeq (k + 1)
  let zk : E := z_k Q f d L σ α xSeq k
  let g : Module.Dual ℝ E := (fderiv ℝ f (xSeq (k + 1))).toLinearMap
  let model : E → ℝ := fun y => DualPairing g (y - xk1) + (L / 2) * ‖y - xk1‖ ^ 2
  have hpoint :
      ∀ z ∈ Q,
        A * f (ySeq (k + 1)) ≤
          (L / σ) * d z +
            Finset.sum (Finset.range (k + 2)) (fun i =>
              α i * (f (xSeq i) +
                DualPairing ((fderiv ℝ f (xSeq i)).toLinearMap) (z - xSeq i))) := by
    intro z hz
    have hmodel_ge :
        model (ySeq (k + 1) : E) ≥ f (ySeq (k + 1)) - f xk1 := by
      have h :=
        section03_model_at_TQ_ge_fdiff (hQ_convex := hQ_convex) (hf_diff := hf_diff)
          (hL := hL) (hgrad_lipschitz := hgrad_lipschitz) (x0 := xSeq (k + 1))
      have h' : model (T_Q Q f L (xSeq (k + 1)) : E) ≥
          f (T_Q Q f L (xSeq (k + 1))) - f xk1 := by
        simpa [model, g, xk1] using h
      simpa [hy_update] using h'
    have hfy_le : f (ySeq (k + 1)) ≤ f xk1 + model (ySeq (k + 1) : E) := by
      linarith [hmodel_ge]
    have hfy_mul :
        A * f (ySeq (k + 1)) ≤ A * (f xk1 + model (ySeq (k + 1) : E)) := by
      exact mul_le_mul_of_nonneg_left hfy_le hA_nonneg
    let y : E := τ • z + (1 - τ) • (ySeq k : E)
    have hy_data :
        y ∈ Q ∧ y - xk1 = τ • (z - zk) := by
      have h :=
        section03_change_of_variables_y (hQ_convex := hQ_convex) (α := α) (xSeq := xSeq)
          (ySeq := ySeq) (k := k) (x := z) (hx := hz) (hτ_nonneg := hτ_nonneg)
          (hτ_le := hτ_le) (hx_update := hx_update)
      simpa [y, τ, xk1, zk] using h
    have hy_mem : y ∈ Q := hy_data.1
    have hy_shift : y - xk1 = τ • (z - zk) := hy_data.2
    have hmodel_le : model (ySeq (k + 1) : E) ≤ model y := by
      have h :=
        R0_TQ_model_le (hQ_closed := hQ_closed) (hL := hL) (f := f) (x0 := xSeq (k + 1)) y
          hy_mem
      have h' : model (T_Q Q f L (xSeq (k + 1)) : E) ≤ model y := by
        simpa [model, g, xk1] using h
      simpa [hy_update] using h'
    have hmodel_le_mul :
        A * (f xk1 + model (ySeq (k + 1) : E)) ≤ A * (f xk1 + model y) := by
      have hadd : f xk1 + model (ySeq (k + 1) : E) ≤ f xk1 + model y := by
        have h := add_le_add_left hmodel_le (f xk1)
        simpa [add_comm, add_left_comm, add_assoc] using h
      exact mul_le_mul_of_nonneg_left hadd hA_nonneg
    have hmodel_eq :
        model y =
          (L / 2) * τ ^ 2 * ‖z - zk‖ ^ 2 + τ * DualPairing g (z - zk) := by
      have h :=
        section03_change_of_variables_model (α := α) (xSeq := xSeq) (k := k)
          (x := z) (y := y) (τ := τ) (hy_shift := hy_shift) g
      calc
        model y = DualPairing g (y - xk1) + (L / 2) * ‖y - xk1‖ ^ 2 := rfl
        _ = (L / 2) * ‖y - xk1‖ ^ 2 + DualPairing g (y - xk1) := by
          ac_rfl
        _ = (L / 2) * τ ^ 2 * ‖z - zk‖ ^ 2 + τ * DualPairing g (z - zk) := by
          simpa [xk1, zk, y] using h.symm
    have hcoeff :
        A * ((L / 2) * τ ^ 2 * ‖z - zk‖ ^ 2 + τ * DualPairing g (z - zk)) ≤
          (L / 2) * ‖z - zk‖ ^ 2 + α (k + 1) * DualPairing g (z - zk) := by
      have hcoeff_base :
          (L / 2) * τ ^ 2 * ‖z - zk‖ ^ 2 ≤ (L / (2 * A)) * ‖z - zk‖ ^ 2 := by
        have h :=
          section03_quad_coeff_compare (L := L) (A := A) (τ := τ) (hL := le_of_lt hL)
            (hA := hA_pos) (hτ := hτ_sq) (v := (z - zk))
        simpa [ge_iff_le] using h
      have hcoeff_add :
          (L / 2) * τ ^ 2 * ‖z - zk‖ ^ 2 + τ * DualPairing g (z - zk) ≤
            (L / (2 * A)) * ‖z - zk‖ ^ 2 + τ * DualPairing g (z - zk) := by
        have h := add_le_add_right hcoeff_base (τ * DualPairing g (z - zk))
        simpa [add_comm, add_left_comm, add_assoc] using h
      have hcoeff_mul :
          A * ((L / 2) * τ ^ 2 * ‖z - zk‖ ^ 2 + τ * DualPairing g (z - zk)) ≤
            A * ((L / (2 * A)) * ‖z - zk‖ ^ 2 + τ * DualPairing g (z - zk)) := by
        exact mul_le_mul_of_nonneg_left hcoeff_add hA_nonneg
      have hAtau : A * τ = α (k + 1) := by
        calc
          A * τ = A * (α (k + 1) / A) := by simp [τ]
          _ = α (k + 1) := by
            field_simp [hA_ne]
      have hcoeff_simp :
          A * ((L / (2 * A)) * ‖z - zk‖ ^ 2 + τ * DualPairing g (z - zk)) =
            (L / 2) * ‖z - zk‖ ^ 2 + α (k + 1) * DualPairing g (z - zk) := by
        calc
          A * ((L / (2 * A)) * ‖z - zk‖ ^ 2 + τ * DualPairing g (z - zk)) =
              A * ((L / (2 * A)) * ‖z - zk‖ ^ 2) + A * (τ * DualPairing g (z - zk)) := by
                simp [mul_add, add_comm]
          _ = (L / 2) * ‖z - zk‖ ^ 2 + (A * τ) * DualPairing g (z - zk) := by
                field_simp [hA_ne, mul_comm, mul_left_comm, mul_assoc]
          _ = (L / 2) * ‖z - zk‖ ^ 2 + α (k + 1) * DualPairing g (z - zk) := by
                simp [hAtau, mul_comm]
      exact le_trans hcoeff_mul (by simp [hcoeff_simp])
    have hmodel_bound :
        A * f (ySeq (k + 1)) ≤
          A * f xk1 + (L / 2) * ‖z - zk‖ ^ 2 + α (k + 1) * DualPairing g (z - zk) := by
      calc
        A * f (ySeq (k + 1)) ≤ A * (f xk1 + model (ySeq (k + 1) : E)) := hfy_mul
        _ ≤ A * (f xk1 + model y) := hmodel_le_mul
        _ = A * (f xk1 + ((L / 2) * τ ^ 2 * ‖z - zk‖ ^ 2 +
            τ * DualPairing g (z - zk))) := by
          simp [hmodel_eq]
        _ = A * f xk1 + A * ((L / 2) * τ ^ 2 * ‖z - zk‖ ^ 2 +
            τ * DualPairing g (z - zk)) := by
          simp [mul_add, add_comm]
        _ ≤ A * f xk1 + (L / 2) * ‖z - zk‖ ^ 2 + α (k + 1) * DualPairing g (z - zk) := by
          have h := add_le_add_left hcoeff (A * f xk1)
          simpa [add_comm, add_left_comm, add_assoc] using h
    have hA_old_nonneg : 0 ≤ A_k α k := by
      unfold A_k
      exact Finset.sum_nonneg (fun i _ => le_of_lt (hα_pos i))
    have hsupport :
        f (ySeq k) ≥ f xk1 + DualPairing g ((ySeq k : E) - xk1) := by
      have hxk1' : (xSeq (k + 1) : E) ∈ Q := (xSeq (k + 1)).property
      have hyk' : (ySeq k : E) ∈ Q := (ySeq k).property
      exact
        section03_convex_support_fderiv (hQ_convex := hQ_convex) (hf_convex := hf_convex)
          (u := (ySeq k : E)) (v := (xSeq (k + 1) : E)) hyk' hxk1'
          (hf_diff (xSeq (k + 1)) hxk1')
    have hsupport_scaled :
        A_k α k * (f xk1 + DualPairing g ((ySeq k : E) - xk1)) ≤
          A_k α k * f (ySeq k) := by
      exact mul_le_mul_of_nonneg_left hsupport hA_old_nonneg
    have hpsi_linear :
        A_k α k * (f xk1 + DualPairing g ((ySeq k : E) - xk1)) ≤
          psi_k Q f d L σ α xSeq k := by
      exact le_trans hsupport_scaled hRk
    have hpsi_plus :
        A_k α k * (f xk1 + DualPairing g ((ySeq k : E) - xk1)) +
            α (k + 1) * (f xk1 + DualPairing g (z - xk1)) ≤
          psi_k Q f d L σ α xSeq k + α (k + 1) * (f xk1 + DualPairing g (z - xk1)) := by
      have h := add_le_add_right hpsi_linear (α (k + 1) * (f xk1 + DualPairing g (z - xk1)))
      simpa [add_comm, add_left_comm, add_assoc] using h
    have hcombine :
        A_k α k * DualPairing g ((ySeq k : E) - xk1) +
            α (k + 1) * DualPairing g (z - xk1) =
          α (k + 1) * DualPairing g (z - zk) := by
      have h :=
        section03_dualpairing_combine_update (α := α) (xSeq := xSeq) (ySeq := ySeq)
          (k := k) (hA_pos := hA_pos) (hx_update := hx_update) g z
      simpa [xk1, zk] using h
    have hA_sum : A = A_k α k + α (k + 1) := by
      simp [A, A_k, Finset.sum_range_succ, add_comm, add_left_comm, add_assoc]
    have hpsi_plus' :
        A * f xk1 + α (k + 1) * DualPairing g (z - zk) ≤
          psi_k Q f d L σ α xSeq k + α (k + 1) * (f xk1 + DualPairing g (z - xk1)) := by
      calc
        A * f xk1 + α (k + 1) * DualPairing g (z - zk) =
            A_k α k * (f xk1 + DualPairing g ((ySeq k : E) - xk1)) +
              α (k + 1) * (f xk1 + DualPairing g (z - xk1)) := by
          calc
            A * f xk1 + α (k + 1) * DualPairing g (z - zk) =
                (A_k α k + α (k + 1)) * f xk1 + α (k + 1) * DualPairing g (z - zk) := by
              simp [hA_sum]
            _ =
                A_k α k * f xk1 + α (k + 1) * f xk1 +
                  α (k + 1) * DualPairing g (z - zk) := by
              ring
            _ =
                A_k α k * f xk1 + α (k + 1) * f xk1 +
                  (A_k α k * DualPairing g ((ySeq k : E) - xk1) +
                    α (k + 1) * DualPairing g (z - xk1)) := by
              simp [hcombine]
            _ =
                A_k α k * (f xk1 + DualPairing g ((ySeq k : E) - xk1)) +
                  α (k + 1) * (f xk1 + DualPairing g (z - xk1)) := by
              ring
        _ ≤ psi_k Q f d L σ α xSeq k + α (k + 1) * (f xk1 + DualPairing g (z - xk1)) := by
          exact hpsi_plus
    have hpsi_plus'' :
        A * f xk1 + (L / 2) * ‖z - zk‖ ^ 2 + α (k + 1) * DualPairing g (z - zk) ≤
          psi_k Q f d L σ α xSeq k + (L / 2) * ‖z - zk‖ ^ 2 +
            α (k + 1) * (f xk1 + DualPairing g (z - xk1)) := by
      have h := add_le_add_right hpsi_plus' ((L / 2) * ‖z - zk‖ ^ 2)
      simpa [add_comm, add_left_comm, add_assoc] using h
    have hFk_lower :=
      section03_Fk_quadratic_lower_bound_at_zk (α := α) (xSeq := xSeq) (k := k)
        (hQ_convex := hQ_convex) (hconv := hconv) (hσ := hσ) (hL := hL) (hα_pos := hα_pos)
        (hzk_min := hzk_min) z hz
    have hFk1_lower :
        psi_k Q f d L σ α xSeq k + (L / 2) * ‖z - zk‖ ^ 2 +
            α (k + 1) * (f xk1 + DualPairing g (z - xk1)) ≤
          (L / σ) * d z +
            Finset.sum (Finset.range (k + 2)) (fun i =>
              α i * (f (xSeq i) +
                DualPairing ((fderiv ℝ f (xSeq i)).toLinearMap) (z - xSeq i))) := by
      let term : ℕ → ℝ := fun i =>
        α i * (f (xSeq i) +
          DualPairing ((fderiv ℝ f (xSeq i)).toLinearMap) (z - xSeq i))
      have h' :
          psi_k Q f d L σ α xSeq k + (L / 2) * ‖z - zk‖ ^ 2 +
              α (k + 1) * (f xk1 + DualPairing g (z - xk1)) ≤
            (L / σ) * d z + Finset.sum (Finset.range (k + 1)) term +
              α (k + 1) * (f xk1 + DualPairing g (z - xk1)) := by
        have h :=
          add_le_add_right hFk_lower (α (k + 1) * (f xk1 + DualPairing g (z - xk1)))
        simpa [add_comm, add_left_comm, add_assoc] using h
      have h'' :
          psi_k Q f d L σ α xSeq k + (L / 2) * ‖z - zk‖ ^ 2 +
              α (k + 1) * (f xk1 + DualPairing g (z - xk1)) ≤
            (L / σ) * d z + Finset.sum (Finset.range (k + 1)) term + term (k + 1) := by
        simpa [term, xk1, g, add_assoc] using h'
      simpa [term, Finset.sum_range_succ, add_assoc] using h''
    exact le_trans (le_trans hmodel_bound hpsi_plus'') hFk1_lower
  unfold R_k
  simp [psi_k]
  refine le_csInf ?_ ?_
  · refine ⟨(L / σ) * d (xSeq (k + 1)) +
      Finset.sum (Finset.range (k + 2)) (fun i =>
        α i * (f (xSeq i) +
          DualPairing ((fderiv ℝ f (xSeq i)).toLinearMap) ((xSeq (k + 1) : E) - xSeq i))), ?_⟩
    exact ⟨(xSeq (k + 1) : E), (xSeq (k + 1)).property, rfl⟩
  · intro b hb
    rcases hb with ⟨z, hz, rfl⟩
    simpa [A] using hpoint z hz

/-- Closed form for `A_k` when `α_k = (k+1)/2`. -/
lemma section03_Ak_alpha_closed_form (k : ℕ) :
    A_k (fun k => ((k : ℝ) + 1) / 2) k =
      ((k : ℝ) + 1) * ((k : ℝ) + 2) / 4 := by
  induction k with
  | zero =>
      simp [A_k]
      norm_num
  | succ k ih =>
      have hsum :
          A_k (fun k => ((k : ℝ) + 1) / 2) (k + 1) =
            A_k (fun k => ((k : ℝ) + 1) / 2) k + ((k : ℝ) + 2) / 2 := by
        simp [A_k, Finset.sum_range_succ, add_comm, add_left_comm]
        ring
      have hcalc :
          A_k (fun k => ((k : ℝ) + 1) / 2) (k + 1) =
            ((k : ℝ) + 1 + 1) * ((k : ℝ) + 1 + 2) / 4 := by
        calc
          A_k (fun k => ((k : ℝ) + 1) / 2) (k + 1) =
              A_k (fun k => ((k : ℝ) + 1) / 2) k + ((k : ℝ) + 2) / 2 := hsum
          _ =
              ((k : ℝ) + 1) * ((k : ℝ) + 2) / 4 + ((k : ℝ) + 2) / 2 := by
            simp [ih]
          _ = ((k : ℝ) + 2) * ((k : ℝ) + 3) / 4 := by
            have h2 : (2 : ℝ) ≠ 0 := by norm_num
            have h4 : (4 : ℝ) ≠ 0 := by norm_num
            field_simp [h2, h4]
            ring
          _ = ((k : ℝ) + 1 + 1) * ((k : ℝ) + 1 + 2) / 4 := by
            ring
      simpa [add_assoc, add_left_comm, add_comm] using hcalc

/-- Closed form for `τ_k = α_{k+1}/A_{k+1}` when `α_k = (k+1)/2`. -/
lemma section03_tau_alpha_closed_form (k : ℕ) :
    (fun k => ((k : ℝ) + 1) / 2) (k + 1) /
        A_k (fun k => ((k : ℝ) + 1) / 2) (k + 1) =
      2 / ((k : ℝ) + 3) := by
  have hAk :
      A_k (fun k => ((k : ℝ) + 1) / 2) (k + 1) =
        ((k : ℝ) + 2) * ((k : ℝ) + 3) / 4 := by
    calc
      A_k (fun k => ((k : ℝ) + 1) / 2) (k + 1) =
          ((k : ℝ) + 1 + 1) * ((k : ℝ) + 1 + 2) / 4 := by
        simpa using section03_Ak_alpha_closed_form (k + 1)
      _ = ((k : ℝ) + 2) * ((k : ℝ) + 3) / 4 := by
        ring
  have hk2_pos : 0 < (k : ℝ) + 2 := by
    have hk_nonneg : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Nat.zero_le k)
    linarith
  have hk3_pos : 0 < (k : ℝ) + 3 := by
    have hk_nonneg : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Nat.zero_le k)
    linarith
  have hk2_ne : (k : ℝ) + 2 ≠ 0 := ne_of_gt hk2_pos
  have hk3_ne : (k : ℝ) + 3 ≠ 0 := ne_of_gt hk3_pos
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  have h4 : (4 : ℝ) ≠ 0 := by norm_num
  have hnum : (k : ℝ) + 1 + 1 = (k : ℝ) + 2 := by
    ring
  calc
    (fun k => ((k : ℝ) + 1) / 2) (k + 1) /
        A_k (fun k => ((k : ℝ) + 1) / 2) (k + 1) =
        ((k : ℝ) + 2) / 2 / (((k : ℝ) + 2) * ((k : ℝ) + 3) / 4) := by
      simp [hAk, hnum]
    _ = 2 / ((k : ℝ) + 3) := by
      field_simp [hk2_ne, hk3_ne, h2, h4]
      ring

/-- The initial step size satisfies `α_0 ∈ (0,1]`. -/
lemma section03_alpha0_mem_Ioc :
    (fun k => ((k : ℝ) + 1) / 2) 0 ∈ Set.Ioc (0 : ℝ) 1 := by
  simp [Set.mem_Ioc]
  norm_num

/-- The inequality `α_{k+1}^2 ≤ A_{k+1}` for `α_k = (k+1)/2`. -/
lemma section03_alpha_sq_le_Ak (k : ℕ) :
    (fun k => ((k : ℝ) + 1) / 2) (k + 1) ^ 2 ≤
      A_k (fun k => ((k : ℝ) + 1) / 2) (k + 1) := by
  have hAk :
      A_k (fun k => ((k : ℝ) + 1) / 2) (k + 1) =
        ((k : ℝ) + 2) * ((k : ℝ) + 3) / 4 := by
    calc
      A_k (fun k => ((k : ℝ) + 1) / 2) (k + 1) =
          ((k : ℝ) + 1 + 1) * ((k : ℝ) + 1 + 2) / 4 := by
        simpa using section03_Ak_alpha_closed_form (k + 1)
      _ = ((k : ℝ) + 2) * ((k : ℝ) + 3) / 4 := by
        ring
  have hk_nonneg : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Nat.zero_le k)
  have hk2_nonneg : 0 ≤ (k : ℝ) + 2 := by linarith
  have hk2_le : (k : ℝ) + 2 ≤ (k : ℝ) + 3 := by linarith
  have hineq : ((k : ℝ) + 2) ^ 2 ≤ ((k : ℝ) + 2) * ((k : ℝ) + 3) := by
    have h := mul_le_mul_of_nonneg_left hk2_le hk2_nonneg
    simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using h
  have hquarter : (0 : ℝ) ≤ (4 : ℝ)⁻¹ := by norm_num
  have hineq' :
      ((k : ℝ) + 2) ^ 2 / 4 ≤ ((k : ℝ) + 2) * ((k : ℝ) + 3) / 4 := by
    have h := mul_le_mul_of_nonneg_right hineq hquarter
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
  calc
    (fun k => ((k : ℝ) + 1) / 2) (k + 1) ^ 2 = (((k : ℝ) + 2) / 2) ^ 2 := by
      have hnum : (k : ℝ) + 1 + 1 = (k : ℝ) + 2 := by
        ring
      simp [hnum]
    _ = ((k : ℝ) + 2) ^ 2 / 4 := by
      have h2 : (2 : ℝ) ≠ 0 := by norm_num
      field_simp [h2]
      ring
    _ ≤ A_k (fun k => ((k : ℝ) + 1) / 2) (k + 1) := by
      simpa [hAk] using hineq'

/-- Lemma 1.3.2.
For `k ≥ 0`, define `α_k = (k+1)/2` (equation (alpha_k_def)). Then
`τ_k = 2/(k+3)` and `A_k = (k+1)(k+2)/4` (equation (3.10)), and the conditions (3.6)
(`α_0 ∈ (0,1]` and `α_{k+1}^2 ≤ A_{k+1}`) are satisfied. -/
theorem alpha_seq_closed_form :
    let α : ℕ → ℝ := fun k => ((k : ℝ) + 1) / 2
    (∀ k, A_k α k = ((k : ℝ) + 1) * ((k : ℝ) + 2) / 4) ∧
    (∀ k, α (k + 1) / A_k α (k + 1) = 2 / ((k : ℝ) + 3)) ∧
    α 0 ∈ Set.Ioc (0 : ℝ) 1 ∧
    (∀ k, (α (k + 1)) ^ 2 ≤ A_k α (k + 1)) := by
  simp
  refine ⟨?_, ?_⟩
  · intro k
    simpa using section03_Ak_alpha_closed_form k
  · refine ⟨?_, ?_⟩
    · intro k
      simpa using section03_tau_alpha_closed_form k
    · refine ⟨?_, ?_⟩
      · simpa using section03_alpha0_mem_Ioc
      · intro k
        simpa using section03_alpha_sq_le_Ak k

/-- Algorithm 1.3.1.
Assume `f` satisfies (grad_lipschitz) on `Q`, and let `d` be a prox-function for `Q` with
parameter `σ`. Initialize at a prox-center `x0` of `Q` and set `y0 = T_Q(x0)`. For `k ≥ 0`,
iterate:
1) compute `f(x_k)` and `∇ f(x_k)`;
2) compute `y_k = T_Q(x_k)`;
3) compute `z_k` as an argmin of
   `(L/σ) d(x) + ∑_{i=0}^k (i+1)/2 [ f(x_i) + ⟪∇ f(x_i), x - x_i⟫ ]` over `x ∈ Q`
   (equation (alg311:zk));
4) set `x_{k+1} = (2/(k+3)) z_k + ((k+1)/(k+3)) y_k` (equation (3.11)). -/
def OptimalSchemeAlgorithm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (Q : Set E) (f d : E → ℝ) (L σ : ℝ)
    (xSeq ySeq : ℕ → Q) : Prop :=
  IsClosed Q ∧
  ConvexOn ℝ Q f ∧
  (∀ x ∈ Q, DifferentiableAt ℝ f x) ∧
  0 < L ∧
  (∀ x ∈ Q, ∀ y ∈ Q,
      DualNormDef ((fderiv ℝ f x).toLinearMap - (fderiv ℝ f y).toLinearMap) ≤
        L * ‖x - y‖) ∧
  ProxFunction Q d ∧ StrongConvexOn Q σ d ∧ 0 < σ ∧
  IsNormalizedProxCenter Q d (xSeq 0) ∧
  ySeq 0 = T_Q Q f L (xSeq 0) ∧
  (∀ k, ySeq k = T_Q Q f L (xSeq k)) ∧
  (∀ k,
    IsMinOn
      (fun x : E =>
        (L / σ) * d x +
          Finset.sum (Finset.range (k + 1)) (fun i =>
            ((i : ℝ) + 1) / 2 *
              (f (xSeq i) +
                DualPairing ((fderiv ℝ f (xSeq i)).toLinearMap) (x - xSeq i))))
      Q (z_k Q f d L σ (fun i => ((i : ℝ) + 1) / 2) xSeq k : E)) ∧
  (∀ k, (xSeq (k + 1) : E) =
    (2 / ((k : ℝ) + 3)) • (z_k Q f d L σ (fun i => ((i : ℝ) + 1) / 2) xSeq k : E) +
      (((k : ℝ) + 1) / ((k : ℝ) + 3)) • (ySeq k : E))

/-- Definition 1.3.6.
Define a modified selection rule: given `y_{k-1}`, set `\tilde y_k = T_Q(x_k)` and choose
`y_k ∈ argmin { f x : x ∈ {y_{k-1}, x_k, \tilde y_k} }` (equation (3.14)). -/
def ModifiedSelectionRule {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (Q : Set E) (f : E → ℝ) (L : ℝ)
    (xSeq ySeq : ℕ → Q) (k : ℕ) : Prop :=
  let ytilde : Q := T_Q Q f L (xSeq (Nat.succ k))
  let S : Set Q := ({ySeq k} ∪ {xSeq (Nat.succ k)} ∪ {ytilde})
  ySeq (Nat.succ k) ∈ S ∧ ∀ z ∈ S, f (ySeq (Nat.succ k)) ≤ f z

/-- Proposition 1.3.5.
If `{y_k}` is chosen by the rule (3.14), then
`f(y_k) ≤ f(y_{k-1}) ≤ ⋯ ≤ f(x_0)` (equation (3.15)). -/
theorem modified_selection_rule_monotone {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {Q : Set E} {f : E → ℝ} {L : ℝ}
    (xSeq ySeq : ℕ → Q) (hselect : ∀ k, ModifiedSelectionRule Q f L xSeq ySeq k)
    (h0 : f (ySeq 0) ≤ f (xSeq 0)) :
    (∀ k, f (ySeq (k + 1)) ≤ f (ySeq k)) ∧ (∀ k, f (ySeq k) ≤ f (xSeq 0)) := by
  have hmono_succ : ∀ k, f (ySeq (Nat.succ k)) ≤ f (ySeq k) := by
    intro k
    have hsel := hselect k
    dsimp [ModifiedSelectionRule] at hsel
    rcases hsel with ⟨_, hy_min⟩
    have hyk_mem :
        ySeq k ∈
          (({ySeq k} : Set Q) ∪ {xSeq (Nat.succ k)} ∪
            {T_Q Q f L (xSeq (Nat.succ k))}) := by
      simp
    exact hy_min (ySeq k) hyk_mem
  have hmono : ∀ k, f (ySeq (k + 1)) ≤ f (ySeq k) := by
    intro k
    exact hmono_succ k
  have hbound_to_y0 : ∀ k, f (ySeq k) ≤ f (ySeq 0) := by
    intro k
    induction k with
    | zero =>
        simp
    | succ k hk =>
        exact le_trans (hmono_succ k) hk
  have hbound : ∀ k, f (ySeq k) ≤ f (xSeq 0) := by
    intro k
    exact le_trans (hbound_to_y0 k) h0
  exact ⟨hmono, hbound⟩

/-- The infimum defining `ψ_k` is bounded above by evaluation at any feasible point. -/
lemma section03_psi_k_le_eval_of_isMinOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {Q : Set E} {f d : E → ℝ} {L σ : ℝ} (α : ℕ → ℝ)
    (xSeq : ℕ → Q) (k : ℕ)
    (hzk_min :
      IsMinOn
        (fun x : E =>
          (L / σ) * d x +
            Finset.sum (Finset.range (k + 1)) (fun i =>
              α i * (f (xSeq i) +
                DualPairing ((fderiv ℝ f (xSeq i)).toLinearMap) (x - xSeq i))))
        Q (z_k Q f d L σ α xSeq k : E)) :
    ∀ x ∈ Q,
      psi_k Q f d L σ α xSeq k ≤
        (L / σ) * d x +
          Finset.sum (Finset.range (k + 1)) (fun i =>
            α i * (f (xSeq i) +
              DualPairing ((fderiv ℝ f (xSeq i)).toLinearMap) (x - xSeq i))) := by
  classical
  let Fk : E → ℝ := fun x =>
    (L / σ) * d x +
      Finset.sum (Finset.range (k + 1)) (fun i =>
        α i * (f (xSeq i) +
          DualPairing ((fderiv ℝ f (xSeq i)).toLinearMap) (x - xSeq i)))
  have hBdd : BddBelow (Fk '' Q) := by
    refine ⟨Fk (z_k Q f d L σ α xSeq k : E), ?_⟩
    intro b hb
    rcases hb with ⟨z, hz, rfl⟩
    have hmin := (isMinOn_iff.mp hzk_min) z hz
    simpa [Fk] using hmin
  intro x hx
  have hpsi_le : psi_k Q f d L σ α xSeq k ≤ Fk x := by
    refine csInf_le hBdd ?_
    exact ⟨x, hx, rfl⟩
  simpa [psi_k, Fk] using hpsi_le

/-- Upper bound `ψ_k` by evaluating the affine model at a point `x★ ∈ Q`. -/
lemma section03_psik_upper_bound_at_xstar {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {Q : Set E} {f d : E → ℝ} {L σ : ℝ} (α : ℕ → ℝ)
    (xSeq : ℕ → Q) (k : ℕ) (hQ_convex : Convex ℝ Q) (hf_convex : ConvexOn ℝ Q f)
    (hf_diff : ∀ x ∈ Q, DifferentiableAt ℝ f x) (hα_pos : ∀ k, 0 < α k)
    (hzk_min :
      IsMinOn
        (fun x : E =>
          (L / σ) * d x +
            Finset.sum (Finset.range (k + 1)) (fun i =>
              α i * (f (xSeq i) +
                DualPairing ((fderiv ℝ f (xSeq i)).toLinearMap) (x - xSeq i))))
        Q (z_k Q f d L σ α xSeq k : E)) :
    ∀ xstar ∈ Q,
      psi_k Q f d L σ α xSeq k ≤ (L / σ) * d xstar + A_k α k * f xstar := by
  classical
  intro xstar hxstar
  have hpsi_le :=
    section03_psi_k_le_eval_of_isMinOn (α := α) (xSeq := xSeq) (k := k) (hzk_min := hzk_min)
      xstar hxstar
  have hsum_le :
      Finset.sum (Finset.range (k + 1)) (fun i =>
        α i * (f (xSeq i) +
          DualPairing ((fderiv ℝ f (xSeq i)).toLinearMap) (xstar - xSeq i))) ≤
        Finset.sum (Finset.range (k + 1)) (fun i => α i * f xstar) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    have hx_i : (xSeq i : E) ∈ Q := (xSeq i).property
    have hsupport :
        f xstar ≥ f (xSeq i) +
          DualPairing ((fderiv ℝ f (xSeq i)).toLinearMap) (xstar - xSeq i) := by
      exact
        section03_convex_support_fderiv (hQ_convex := hQ_convex) (hf_convex := hf_convex)
          (u := xstar) (v := (xSeq i : E)) hxstar hx_i (hf_diff (xSeq i) hx_i)
    have hα_nonneg : 0 ≤ α i := le_of_lt (hα_pos i)
    exact mul_le_mul_of_nonneg_left hsupport hα_nonneg
  have hsum_eq :
      Finset.sum (Finset.range (k + 1)) (fun i => α i * f xstar) =
        A_k α k * f xstar := by
    have hsum :=
      (Finset.sum_mul (s := Finset.range (k + 1)) (f := α) (a := f xstar))
    simpa [A_k, mul_comm, mul_left_comm, mul_assoc] using hsum.symm
  have hpsi_le' :
      psi_k Q f d L σ α xSeq k ≤
        (L / σ) * d xstar +
          Finset.sum (Finset.range (k + 1)) (fun i => α i * f xstar) := by
    have h := add_le_add_left hsum_le ((L / σ) * d xstar)
    exact le_trans hpsi_le (by simpa [add_comm, add_left_comm, add_assoc] using h)
  calc
    psi_k Q f d L σ α xSeq k ≤
        (L / σ) * d xstar +
          Finset.sum (Finset.range (k + 1)) (fun i => α i * f xstar) := hpsi_le'
    _ = (L / σ) * d xstar + A_k α k * f xstar := by
        simp [hsum_eq]

/-- Convert `R_k` and an upper bound on `ψ_k` into a gap estimate. -/
lemma section03_rate_bound_from_Rk_and_psik_upper {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {Q : Set E} {f d : E → ℝ} {L σ : ℝ}
    (α : ℕ → ℝ) (xSeq ySeq : ℕ → Q) (xstar : E) (k : ℕ)
    (hA_pos : 0 < A_k α k)
    (hRk : R_k Q f d L σ α xSeq ySeq k)
    (hpsi :
      psi_k Q f d L σ α xSeq k ≤ (L / σ) * d xstar + A_k α k * f xstar) :
    f (ySeq k) - f xstar ≤ (L / σ) * d xstar / A_k α k := by
  have hcombine :
      A_k α k * f (ySeq k) ≤ (L / σ) * d xstar + A_k α k * f xstar := by
    exact le_trans hRk hpsi
  have hgap :
      A_k α k * (f (ySeq k) - f xstar) ≤ (L / σ) * d xstar := by
    linarith
  have hgap' :
      (f (ySeq k) - f xstar) * A_k α k ≤ (L / σ) * d xstar := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hgap
  have hA_ne : A_k α k ≠ 0 := ne_of_gt hA_pos
  have hAinv_pos : 0 < (A_k α k)⁻¹ := inv_pos.mpr hA_pos
  have hgap'' :=
    mul_le_mul_of_nonneg_right hgap' (le_of_lt hAinv_pos)
  have hgap''' :
      f (ySeq k) - f xstar ≤ (L / σ) * d xstar / A_k α k := by
    simpa [div_eq_mul_inv, mul_assoc, hA_ne] using hgap''
  exact hgap'''

/-- The invariant `R_k` holds for all iterates of the optimal scheme. -/
lemma section03_optimalScheme_Rk_all {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {Q : Set E} {f d : E → ℝ} {L σ : ℝ}
    (xSeq ySeq : ℕ → Q) (hAlg : OptimalSchemeAlgorithm Q f d L σ xSeq ySeq) :
    ∀ k, R_k Q f d L σ (fun i => ((i : ℝ) + 1) / 2) xSeq ySeq k := by
  classical
  rcases hAlg with
    ⟨hQ_closed, hf_convex, hf_diff, hL, hgrad_lipschitz, hprox, hconv, hσ, hx0, hy0,
      hy_all, hzk_min_all, hx_update_all⟩
  let α : ℕ → ℝ := fun i => ((i : ℝ) + 1) / 2
  have hAlpha :
      (∀ k, A_k α k = ((k : ℝ) + 1) * ((k : ℝ) + 2) / 4) ∧
      (∀ k, α (k + 1) / A_k α (k + 1) = 2 / ((k : ℝ) + 3)) ∧
      α 0 ∈ Set.Ioc (0 : ℝ) 1 ∧
      (∀ k, (α (k + 1)) ^ 2 ≤ A_k α (k + 1)) := by
    simpa [α] using (alpha_seq_closed_form)
  have hτ_formula := hAlpha.2.1
  have hα0 := hAlpha.2.2.1
  have hα_sq := hAlpha.2.2.2
  have hα_pos : ∀ k, 0 < α k := by
    intro k
    have hk_nonneg : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Nat.zero_le k)
    have hk1_pos : 0 < (k : ℝ) + 1 := by linarith
    have h2_pos : (0 : ℝ) < 2 := by norm_num
    simpa [α] using (div_pos hk1_pos h2_pos)
  have hQ_convex : Convex ℝ Q := hconv.1
  have hR0 :
      R_k Q f d L σ α xSeq ySeq 0 := by
    refine
      R0_relation (α := α) (hQ_closed := hQ_closed) (hQ_convex := hQ_convex)
        (hf_diff := hf_diff) (hL := hL) (hgrad_lipschitz := hgrad_lipschitz)
        (hconv := hconv) (hσ := hσ) (xSeq := xSeq) (ySeq := ySeq) (x0 := xSeq 0)
        (hx0 := hx0) (hα0 := hα0) (hxSeq0 := rfl) (hySeq0 := hy0)
  intro k
  induction k with
  | zero =>
      simpa [α] using hR0
  | succ k hk =>
      have hτ :
          α (k + 1) / A_k α (k + 1) = 2 / ((k : ℝ) + 3) := hτ_formula k
      have hτ' :
          1 - α (k + 1) / A_k α (k + 1) = ((k : ℝ) + 1) / ((k : ℝ) + 3) := by
        have hk_nonneg : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Nat.zero_le k)
        have hk3_pos : 0 < (k : ℝ) + 3 := by linarith
        have hk3_ne : (k : ℝ) + 3 ≠ 0 := ne_of_gt hk3_pos
        calc
          1 - α (k + 1) / A_k α (k + 1) = 1 - 2 / ((k : ℝ) + 3) := by
            simp [hτ]
          _ = ((k : ℝ) + 1) / ((k : ℝ) + 3) := by
            field_simp [hk3_ne]
            ring
      have hx_update :
          (xSeq (k + 1) : E) =
            (α (k + 1) / A_k α (k + 1)) •
              (z_k Q f d L σ α xSeq k : E) +
              (1 - α (k + 1) / A_k α (k + 1)) • (ySeq k : E) := by
        have hx := hx_update_all k
        rw [hτ', hτ]
        simpa [α] using hx
      have hy_update : ySeq (k + 1) = T_Q Q f L (xSeq (k + 1)) := by
        simpa using hy_all (k + 1)
      have hzk_min :
          IsMinOn
            (fun x : E =>
              (L / σ) * d x +
                Finset.sum (Finset.range (k + 1)) (fun i =>
                  α i * (f (xSeq i) +
                    DualPairing ((fderiv ℝ f (xSeq i)).toLinearMap) (x - xSeq i))))
            Q (z_k Q f d L σ α xSeq k : E) := by
        simpa [α] using hzk_min_all k
      exact
        Rk_succ_update (α := α) (hQ_closed := hQ_closed) (hQ_convex := hQ_convex)
          (hf_convex := hf_convex) (hf_diff := hf_diff) (hL := hL)
          (hgrad_lipschitz := hgrad_lipschitz) (hconv := hconv) (hσ := hσ) (xSeq := xSeq)
          (ySeq := ySeq) (k := k) (hα_pos := hα_pos) (hα_sq := hα_sq) (hRk := hk)
          (hzk_min := hzk_min) (hx_update := hx_update) (hy_update := hy_update)

/-- Theorem 1.3.1.
Let sequences `{x_k} ⊆ Q` and `{y_k} ⊆ Q` be generated by Algorithm 1.3.1. Then for any `k ≥ 0`,
`((k+1)(k+2)/4) f(y_k) ≤ min_{x ∈ Q} { (L/σ) d x + ∑_{i=0}^k (i+1)/2 [ f(x_i)
+ ⟪∇ f(x_i), x - x_i⟫ ] }` (equation (3.12)). If `x* ∈ argmin_{x ∈ Q} f x`, then
`f(y_k) - f(x*) ≤ 4 L d(x*) / (σ (k+1)(k+2))` (equation (3.13)). -/
theorem optimal_scheme_rate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {Q : Set E} {f d : E → ℝ} {L σ : ℝ}
    (xSeq ySeq : ℕ → Q) (hAlg : OptimalSchemeAlgorithm Q f d L σ xSeq ySeq) :
    (∀ k : ℕ,
      (((k : ℝ) + 1) * ((k : ℝ) + 2) / 4) * f (ySeq k) ≤
        psi_k Q f d L σ (fun i => ((i : ℝ) + 1) / 2) xSeq k) ∧
    (∀ xstar : E, xstar ∈ Q → (∀ y ∈ Q, f xstar ≤ f y) →
      ∀ k : ℕ,
        f (ySeq k) - f xstar ≤
          (4 * L * d xstar) / (σ * ((k : ℝ) + 1) * ((k : ℝ) + 2))) := by
  classical
  have hRk_all :
      ∀ k, R_k Q f d L σ (fun i => ((i : ℝ) + 1) / 2) xSeq ySeq k :=
    section03_optimalScheme_Rk_all (xSeq := xSeq) (ySeq := ySeq) hAlg
  rcases hAlg with
    ⟨hQ_closed, hf_convex, hf_diff, hL, hgrad_lipschitz, hprox, hconv, hσ, hx0, hy0,
      hy_all, hzk_min_all, hx_update_all⟩
  let α : ℕ → ℝ := fun i => ((i : ℝ) + 1) / 2
  have hAlpha :
      (∀ k, A_k α k = ((k : ℝ) + 1) * ((k : ℝ) + 2) / 4) ∧
      (∀ k, α (k + 1) / A_k α (k + 1) = 2 / ((k : ℝ) + 3)) ∧
      α 0 ∈ Set.Ioc (0 : ℝ) 1 ∧
      (∀ k, (α (k + 1)) ^ 2 ≤ A_k α (k + 1)) := by
    simpa [α] using (alpha_seq_closed_form)
  have hA_formula := hAlpha.1
  have hα_pos : ∀ k, 0 < α k := by
    intro k
    have hk_nonneg : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Nat.zero_le k)
    have hk1_pos : 0 < (k : ℝ) + 1 := by linarith
    have h2_pos : (0 : ℝ) < 2 := by norm_num
    simpa [α] using (div_pos hk1_pos h2_pos)
  have hQ_convex : Convex ℝ Q := hconv.1
  refine ⟨?_, ?_⟩
  · intro k
    have hRk := hRk_all k
    have hA_formula' :
        A_k (fun i => ((i : ℝ) + 1) / 2) k =
          ((k : ℝ) + 1) * ((k : ℝ) + 2) / 4 := by
      simpa [α] using hA_formula k
    simpa [R_k, hA_formula'] using hRk
  · intro xstar hxstar hxstar_min k
    have hpsi_upper :
        psi_k Q f d L σ α xSeq k ≤ (L / σ) * d xstar + A_k α k * f xstar := by
      have hzk_min :
          IsMinOn
            (fun x : E =>
              (L / σ) * d x +
                Finset.sum (Finset.range (k + 1)) (fun i =>
                  α i * (f (xSeq i) +
                    DualPairing ((fderiv ℝ f (xSeq i)).toLinearMap) (x - xSeq i))))
            Q (z_k Q f d L σ α xSeq k : E) := by
        simpa [α] using hzk_min_all k
      exact
        section03_psik_upper_bound_at_xstar (α := α) (xSeq := xSeq) (k := k)
          (hQ_convex := hQ_convex) (hf_convex := hf_convex) (hf_diff := hf_diff)
          (hα_pos := hα_pos) (hzk_min := hzk_min) xstar hxstar
    have hA_pos : 0 < A_k α k := by
      have hα_nonneg : ∀ i ∈ Finset.range (k + 1), 0 ≤ α i := by
        intro i hi
        exact le_of_lt (hα_pos i)
      have hmem : 0 ∈ Finset.range (k + 1) := by
        simp
      have hA_ge : α 0 ≤ A_k α k := by
        simpa [A_k] using (Finset.single_le_sum hα_nonneg hmem)
      exact lt_of_lt_of_le (hα_pos 0) hA_ge
    have hgap :=
      section03_rate_bound_from_Rk_and_psik_upper (α := α) (xSeq := xSeq) (ySeq := ySeq)
        (xstar := xstar) (k := k) (hA_pos := hA_pos) (hRk := hRk_all k)
        (hpsi := hpsi_upper)
    have hk_nonneg : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Nat.zero_le k)
    have hk1_pos : 0 < (k : ℝ) + 1 := by linarith
    have hk2_pos : 0 < (k : ℝ) + 2 := by linarith
    have hk1_ne : (k : ℝ) + 1 ≠ 0 := ne_of_gt hk1_pos
    have hk2_ne : (k : ℝ) + 2 ≠ 0 := ne_of_gt hk2_pos
    have hσ_ne : (σ : ℝ) ≠ 0 := ne_of_gt hσ
    have hrewrite :
        (L / σ) * d xstar / A_k α k =
          (4 * L * d xstar) / (σ * ((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
      calc
        (L / σ) * d xstar / A_k α k =
            (L / σ) * d xstar / (((k : ℝ) + 1) * ((k : ℝ) + 2) / 4) := by
          simp [hA_formula k]
        _ = (4 * L * d xstar) / (σ * ((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
          field_simp [hσ_ne, hk1_ne, hk2_ne]
    simpa [hrewrite] using hgap

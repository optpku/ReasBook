/-
Authors: Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Papers/SmoothMinimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib
import SmoothMinimization_Nesterov_2004.section05_part3

open scoped BigOperators

/-- Rewrite the entropy `V_Q` objective on the simplex. -/
lemma V_Q_entropy_objective_rewrite_on_simplex (n : ℕ) (z : standardSimplex n)
    (g : Module.Dual ℝ (Fin n → ℝ)) (hz_pos : ∀ i, 0 < z.1 i) :
    let d : (Fin n → ℝ) → ℝ :=
      fun x => Real.log (n : ℝ) + ∑ i, x i * Real.log (x i)
    let gcoord : Fin n → ℝ := fun i => g (fun j => if j = i then (1 : ℝ) else 0)
    ∀ x ∈ standardSimplex n,
      DualPairing g (x - z) + bregmanDistance d z x =
        (∑ i, x i * Real.log (x i)) + ∑ i, x i * (gcoord i - Real.log (z.1 i)) -
          ∑ i, z.1 i * gcoord i := by
  classical
  intro d gcoord x hx
  have hpair :
      DualPairing g (x - z.1) =
        (∑ i : Fin n, x i * gcoord i) - ∑ i : Fin n, z.1 i * gcoord i := by
    have hpair' :
        DualPairing g (x - z.1) = ∑ i : Fin n, gcoord i * (x i - z.1 i) := by
      simpa [gcoord] using
        (DualPairing_eq_sum_gcoord_standardBasis (n := n) g (x - z.1))
    calc
      DualPairing g (x - z.1) = ∑ i : Fin n, gcoord i * (x i - z.1 i) := hpair'
      _ = (∑ i : Fin n, gcoord i * x i) - ∑ i : Fin n, gcoord i * z.1 i := by
            simp [mul_sub, Finset.sum_sub_distrib]
      _ = (∑ i : Fin n, x i * gcoord i) - ∑ i : Fin n, z.1 i * gcoord i := by
            simp [mul_comm]
  have hbreg :
      bregmanDistance d z x =
        (∑ i : Fin n, x i * Real.log (x i)) - ∑ i : Fin n, x i * Real.log (z.1 i) := by
    have hbreg' :=
      bregmanDistance_entropy_eq_sum_mul_log_div_on_simplex (n := n) (z := z) (x := x) hx hz_pos
    have hz_ne : ∀ i, z.1 i ≠ 0 := fun i => ne_of_gt (hz_pos i)
    calc
      bregmanDistance d z x = ∑ i, x i * Real.log (x i / z.1 i) := by
        simpa [d] using hbreg'
      _ = ∑ i, (x i * Real.log (x i) - x i * Real.log (z.1 i)) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        simpa using (entropySimplex_mul_log_div_eq (u := z.1 i) (v := x i) (hz_ne i))
      _ =
          (∑ i : Fin n, x i * Real.log (x i)) - ∑ i : Fin n, x i * Real.log (z.1 i) := by
        simp [Finset.sum_sub_distrib]
  have hlin :
      ∑ i : Fin n, x i * (gcoord i - Real.log (z.1 i)) =
        (∑ i : Fin n, x i * gcoord i) - ∑ i : Fin n, x i * Real.log (z.1 i) := by
    calc
      ∑ i : Fin n, x i * (gcoord i - Real.log (z.1 i)) =
          ∑ i : Fin n, (x i * gcoord i - x i * Real.log (z.1 i)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            ring
      _ =
          (∑ i : Fin n, x i * gcoord i) - ∑ i : Fin n, x i * Real.log (z.1 i) := by
            simp [Finset.sum_sub_distrib]
  calc
    DualPairing g (x - z) + bregmanDistance d z x =
        (∑ i : Fin n, x i * gcoord i) - ∑ i : Fin n, z.1 i * gcoord i +
          ((∑ i : Fin n, x i * Real.log (x i)) - ∑ i : Fin n, x i * Real.log (z.1 i)) := by
          simp [hpair, hbreg]
    _ =
        (∑ i : Fin n, x i * Real.log (x i)) +
            ((∑ i : Fin n, x i * gcoord i) - ∑ i : Fin n, x i * Real.log (z.1 i)) -
          ∑ i : Fin n, z.1 i * gcoord i := by
          ring
    _ =
        (∑ i : Fin n, x i * Real.log (x i)) + ∑ i : Fin n, x i * (gcoord i - Real.log (z.1 i)) -
          ∑ i : Fin n, z.1 i * gcoord i := by
          simp [hlin]

/-- The softmax candidate minimizes the entropy `V_Q` objective on the simplex. -/
lemma V_Q_entropy_candidate_isMinOn (n : ℕ) (z : standardSimplex n)
    (g : Module.Dual ℝ (Fin n → ℝ)) (hz_pos : ∀ i, 0 < z.1 i) :
    let d : (Fin n → ℝ) → ℝ :=
      fun x => Real.log (n : ℝ) + ∑ i, x i * Real.log (x i)
    let gcoord : Fin n → ℝ := fun i => g (fun j => if j = i then (1 : ℝ) else 0)
    let s : Fin n → ℝ := fun i => Real.log (z.1 i) - gcoord i
    let u : Fin n → ℝ := fun i => Real.exp (s i) / (∑ j, Real.exp (s j))
    u ∈ standardSimplex n ∧
      IsMinOn (fun x => DualPairing g (x - z) + bregmanDistance d z x) (standardSimplex n) u := by
  classical
  intro d gcoord s u
  have hn : 0 < n := by
    cases n with
    | zero =>
        have : (0 : ℝ) = (1 : ℝ) := by
          simpa using z.property.2
        linarith
    | succ n' =>
        exact Nat.succ_pos n'
  have hsoft :=
    entropySimplex_softmax_maximizer (m := n) (μ := 1) (s := s) hn (by norm_num)
  rcases hsoft with ⟨hu_mem, hupper, -⟩
  have hu_mem' : u ∈ standardSimplex n := by
    simpa [u] using hu_mem
  have hupper' :
      ∀ v ∈ standardSimplex n,
        (∑ j : Fin n, v j * s j) - (∑ j : Fin n, v j * Real.log (v j)) ≤
          (∑ j : Fin n, u j * s j) - (∑ j : Fin n, u j * Real.log (u j)) := by
    intro v hv
    have h := hupper v hv
    simpa using h
  let Φ : (Fin n → ℝ) → ℝ := fun x =>
    DualPairing g (x - z) + bregmanDistance d z x
  have hΦ :
      ∀ x ∈ standardSimplex n,
        Φ x =
          (∑ i, x i * Real.log (x i)) + ∑ i, x i * (gcoord i - Real.log (z.1 i)) -
            ∑ i, z.1 i * gcoord i := by
    intro x hx
    simpa [Φ, d, gcoord] using
      (V_Q_entropy_objective_rewrite_on_simplex (n := n) (z := z) (g := g) (hz_pos := hz_pos)
        x hx)
  have hΦ' :
      ∀ x ∈ standardSimplex n,
        Φ x =
          -((∑ j : Fin n, x j * s j) - (∑ j : Fin n, x j * Real.log (x j))) -
            ∑ i, z.1 i * gcoord i := by
    intro x hx
    have hsum_s :
        ∑ i : Fin n, x i * (gcoord i - Real.log (z.1 i)) =
          -∑ i : Fin n, x i * s i := by
      calc
        ∑ i : Fin n, x i * (gcoord i - Real.log (z.1 i)) =
            ∑ i : Fin n, -(x i * (Real.log (z.1 i) - gcoord i)) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              ring
        _ = -∑ i : Fin n, x i * (Real.log (z.1 i) - gcoord i) := by
              simp [Finset.sum_neg_distrib]
        _ = -∑ i : Fin n, x i * s i := by
              simp [s]
    have hΦx := hΦ x hx
    calc
      Φ x =
          (∑ i, x i * Real.log (x i)) + ∑ i, x i * (gcoord i - Real.log (z.1 i)) -
            ∑ i, z.1 i * gcoord i := hΦx
      _ =
          (∑ i, x i * Real.log (x i)) + (-∑ i : Fin n, x i * s i) -
            ∑ i, z.1 i * gcoord i := by
          simp [hsum_s]
      _ =
          (∑ i, x i * Real.log (x i)) - ∑ i : Fin n, x i * s i -
            ∑ i, z.1 i * gcoord i := by
          ring
      _ =
          -((∑ j : Fin n, x j * s j) - (∑ j : Fin n, x j * Real.log (x j))) -
            ∑ i, z.1 i * gcoord i := by
          ring
  have hmin : IsMinOn Φ (standardSimplex n) u := by
    intro v hv
    have hΨ :
        -((∑ j : Fin n, u j * s j) - (∑ j : Fin n, u j * Real.log (u j))) ≤
          -((∑ j : Fin n, v j * s j) - (∑ j : Fin n, v j * Real.log (v j))) := by
      have h := hupper' v hv
      linarith
    have hconst :=
      add_le_add_right hΨ (-(∑ i : Fin n, z.1 i * gcoord i))
    have hΦu := hΦ' u hu_mem'
    have hΦv := hΦ' v hv
    simpa [hΦu, hΦv] using hconst
  exact ⟨hu_mem', hmin⟩

/-- The entropy `V_Q` objective is strictly convex on the simplex. -/
lemma V_Q_entropy_objective_strictConvexOn (n : ℕ) (z : standardSimplex n)
    (g : Module.Dual ℝ (Fin n → ℝ)) :
    let d : (Fin n → ℝ) → ℝ :=
      fun x => Real.log (n : ℝ) + ∑ i, x i * Real.log (x i)
    StrictConvexOn ℝ (standardSimplex n)
      (fun x => DualPairing g (x - z) + bregmanDistance d z x) := by
  classical
  intro d
  have hconvex : Convex ℝ (standardSimplex n) := by
    simpa [standardSimplex_eq_stdSimplex] using (convex_stdSimplex ℝ (Fin n))
  have hstrong : StrongConvexOn (standardSimplex n) 1 d := by
    have h :=
      (matrixGame_entropy_prox_parameters (n := n) (m := n))
    simpa [d] using h.1
  have hstrict : StrictConvexOn ℝ (standardSimplex n) d :=
    StrongConvexOn.strictConvexOn hstrong (by norm_num)
  let s : Module.Dual ℝ (Fin n → ℝ) := g - (fderiv ℝ d z.1).toLinearMap
  have hlin : ConvexOn ℝ (standardSimplex n) (fun x => DualPairing s (x - z.1)) := by
    simpa using (section03_convex_dualpairing_sub (hQ_convex := hconvex) s z.1)
  have hstrict' :
      StrictConvexOn ℝ (standardSimplex n)
        (fun x => d x + DualPairing s (x - z.1)) := by
    exact StrictConvexOn.add_convexOn hstrict hlin
  have hstrict'' :
      StrictConvexOn ℝ (standardSimplex n)
        (fun x => (d x + DualPairing s (x - z.1)) + (-d z.1)) := by
    simpa [sub_eq_add_neg] using
      (StrictConvexOn.add_const hstrict' (-d z.1))
  have hrewrite :
      (fun x => DualPairing g (x - z) + bregmanDistance d z x) =
        fun x => (d x + DualPairing s (x - z.1)) + (-d z.1) := by
    funext x
    simp [bregmanDistance, DualPairing, s, sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
      map_add, map_neg]
  simpa [hrewrite] using hstrict''

/-- Proposition 1.5.3.1.
Let `Q = Δ_n` and let the prox-function be the entropy distance
`d(x) = ln n + ∑ i x^{(i)} ln x^{(i)}`. Then for `z ∈ Δ_n` and `g ∈ ℝ^n`, the mapping
`V_Q(z,g)` from Definition 1.5.3.1 has the explicit form
`V_Q^{(i)}(z,g) = z^{(i)} e^{-g^{(i)}} [∑_j z^{(j)} e^{-g^{(j)}}]^{-1}`, `i = 1, …, n`
(equation (5.7)). -/
theorem V_Q_entropy_simplex_explicit (n : ℕ) (z : standardSimplex n)
    (g : Module.Dual ℝ (Fin n → ℝ)) (hz_pos : ∀ i, 0 < z.1 i) :
    let d : (Fin n → ℝ) → ℝ :=
      fun x => Real.log (n : ℝ) + ∑ i, x i * Real.log (x i)
    let gcoord : Fin n → ℝ := fun i => g (fun j => if j = i then (1 : ℝ) else 0)
    ∀ i : Fin n,
      (V_Q (standardSimplex n) d z g : Fin n → ℝ) i =
        z.1 i * Real.exp (-gcoord i) / (∑ j, z.1 j * Real.exp (-gcoord j)) := by
  classical
  intro d gcoord i
  let s : Fin n → ℝ := fun j => Real.log (z.1 j) - gcoord j
  let u : Fin n → ℝ := fun j => Real.exp (s j) / (∑ k, Real.exp (s k))
  have hu_min :
      u ∈ standardSimplex n ∧
        IsMinOn (fun x => DualPairing g (x - z) + bregmanDistance d z x)
          (standardSimplex n) u := by
    simpa [d, gcoord, s, u] using
      (V_Q_entropy_candidate_isMinOn (n := n) (z := z) (g := g) (hz_pos := hz_pos))
  have hmin_exists :
      ∃ x : standardSimplex n,
        IsMinOn (fun x : Fin n → ℝ => DualPairing g (x - z) + bregmanDistance d z x)
          (standardSimplex n) x := by
    refine ⟨⟨u, hu_min.1⟩, ?_⟩
    simpa using hu_min.2
  have hmin_VQ :
      IsMinOn (fun x : Fin n → ℝ => DualPairing g (x - z) + bregmanDistance d z x)
        (standardSimplex n) (V_Q (standardSimplex n) d z g) := by
    simpa using (V_Q_spec_isMinOn (Q := standardSimplex n) (d := d) z g hmin_exists)
  have hstrict :
      StrictConvexOn ℝ (standardSimplex n)
        (fun x => DualPairing g (x - z) + bregmanDistance d z x) := by
    simpa [d] using
      (V_Q_entropy_objective_strictConvexOn (n := n) (z := z) (g := g))
  have hVQ_eq_u :
      (V_Q (standardSimplex n) d z g : Fin n → ℝ) = u := by
    refine StrictConvexOn.eq_of_isMinOn hstrict hmin_VQ hu_min.2 ?_ ?_
    · exact (V_Q (standardSimplex n) d z g).property
    · exact hu_min.1
  have hsimp : ∀ j, Real.exp (s j) = z.1 j * Real.exp (-gcoord j) := by
    intro j
    have hzj : 0 < z.1 j := hz_pos j
    calc
      Real.exp (s j) = Real.exp (Real.log (z.1 j) - gcoord j) := by rfl
      _ = Real.exp (Real.log (z.1 j)) / Real.exp (gcoord j) := by
            simp [Real.exp_sub]
      _ = z.1 j / Real.exp (gcoord j) := by
            simp [Real.exp_log hzj]
      _ = z.1 j * Real.exp (-gcoord j) := by
            simp [Real.exp_neg, div_eq_mul_inv]
  have hdenom :
      ∑ j, Real.exp (s j) = ∑ j, z.1 j * Real.exp (-gcoord j) := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    exact hsimp j
  have hu_i :
      u i = z.1 i * Real.exp (-gcoord i) / (∑ j, z.1 j * Real.exp (-gcoord j)) := by
    simp [u, hsimp]
  simp [hVQ_eq_u, hu_i]

/-- Support-plane refinement of `R_k` at `x_{k+1}` for the modified update. -/
lemma section05_modified_Rk_support_at_xk1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {Q : Set E} {f d : E → ℝ} {L σ : ℝ} (α : ℕ → ℝ)
    (xSeq ySeq : ℕ → Q) (k : ℕ) (hQ_convex : Convex ℝ Q) (hf_convex : ConvexOn ℝ Q f)
    (hf_diff : ∀ x ∈ Q, DifferentiableAt ℝ f x) (hα_pos : ∀ k, 0 < α k)
    (hRk : R_k Q f d L σ α xSeq ySeq k) :
    let xk1 : E := xSeq (k + 1)
    let g : Module.Dual ℝ E := (fderiv ℝ f (xSeq (k + 1))).toLinearMap
    A_k α k * (f xk1 + DualPairing g ((ySeq k : E) - xk1)) ≤
      psi_k Q f d L σ α xSeq k := by
  classical
  let xk1 : E := xSeq (k + 1)
  let g : Module.Dual ℝ E := (fderiv ℝ f (xSeq (k + 1))).toLinearMap
  have hxk1 : (xSeq (k + 1) : E) ∈ Q := (xSeq (k + 1)).property
  have hyk : (ySeq k : E) ∈ Q := (ySeq k).property
  have hsupport :
      f (ySeq k) ≥ f xk1 + DualPairing g ((ySeq k : E) - xk1) := by
    exact
      section03_convex_support_fderiv (hQ_convex := hQ_convex) (hf_convex := hf_convex)
        (u := (ySeq k : E)) (v := (xSeq (k + 1) : E)) hyk hxk1
        (hf_diff (xSeq (k + 1)) hxk1)
  have hA_nonneg : 0 ≤ A_k α k := by
    unfold A_k
    exact Finset.sum_nonneg (fun i _ => le_of_lt (hα_pos i))
  have hsupport_scaled :
      A_k α k * (f xk1 + DualPairing g ((ySeq k : E) - xk1)) ≤ A_k α k * f (ySeq k) := by
    exact mul_le_mul_of_nonneg_left hsupport hA_nonneg
  simpa [xk1, g] using (le_trans hsupport_scaled hRk)

/-- Combine gradient pairings using the modified `x_{k+1}` update. -/
lemma section05_modified_dualpairing_combine {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {Q : Set E} {f d : E → ℝ} {L σ : ℝ} (α : ℕ → ℝ)
    (xSeq ySeq : ℕ → Q) (k : ℕ) (hA_pos : 0 < A_k α (k + 1))
    (hx_update :
      (xSeq (k + 1) : E) =
        (α (k + 1) / A_k α (k + 1)) • (z_k Q f d L σ α xSeq k : E) +
          (1 - α (k + 1) / A_k α (k + 1)) • (ySeq k : E))
    (g : Module.Dual ℝ E) (x : E) :
    A_k α k * DualPairing g ((ySeq k : E) - (xSeq (k + 1) : E)) +
        α (k + 1) * DualPairing g (x - (xSeq (k + 1) : E)) =
      α (k + 1) * DualPairing g (x - (z_k Q f d L σ α xSeq k : E)) := by
  simpa using
    (section03_dualpairing_combine_update (α := α) (xSeq := xSeq) (ySeq := ySeq) (k := k)
      (hA_pos := hA_pos) (hx_update := hx_update) g x)

/-- Convert the `V_Q` minimizer into the scaled Bregman inequality. -/
lemma section05_VQ_scaled_min_property {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {Q : Set E} {f d : E → ℝ} {L σ : ℝ} (α : ℕ → ℝ)
    (xSeq : ℕ → Q) (k : ℕ) (g : Module.Dual ℝ E)
    (hVQ_min :
      IsMinOn
        (fun x : E =>
          (L / σ) * bregmanDistance d (z_k Q f d L σ α xSeq k : E) x +
            α (k + 1) * DualPairing g (x - (z_k Q f d L σ α xSeq k : E)))
        Q
        (V_Q Q d (z_k Q f d L σ α xSeq k) (((σ / L) * α (k + 1)) • g) : E)) :
    ∀ x ∈ Q,
      (L / σ) * bregmanDistance d (z_k Q f d L σ α xSeq k : E)
          (V_Q Q d (z_k Q f d L σ α xSeq k) (((σ / L) * α (k + 1)) • g) : E) +
        α (k + 1) * DualPairing g
          ((V_Q Q d (z_k Q f d L σ α xSeq k) (((σ / L) * α (k + 1)) • g) : E) -
            (z_k Q f d L σ α xSeq k : E)) ≤
      (L / σ) * bregmanDistance d (z_k Q f d L σ α xSeq k : E) x +
        α (k + 1) * DualPairing g (x - (z_k Q f d L σ α xSeq k : E)) := by
  intro x hx
  exact (isMinOn_iff.mp hVQ_min) x hx

/-- Express `y_{k+1} - x_{k+1}` via the modified prox update. -/
lemma section05_yminusx_equals_tau_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {Q : Set E} {f d : E → ℝ} {L σ : ℝ} (α : ℕ → ℝ)
    (xSeq ySeq : ℕ → Q) (k : ℕ)
    (hx_update :
      (xSeq (k + 1) : E) =
        (α (k + 1) / A_k α (k + 1)) • (z_k Q f d L σ α xSeq k : E) +
          (1 - α (k + 1) / A_k α (k + 1)) • (ySeq k : E))
    (hy_update :
      (ySeq (k + 1) : E) =
        let τk : ℝ := α (k + 1) / A_k α (k + 1)
        let γk : ℝ := (σ / L) * α (k + 1)
        τk •
            (V_Q Q d (z_k Q f d L σ α xSeq k)
                (γk • fderiv ℝ f (xSeq (k + 1))) : E) +
          (1 - τk) • (ySeq k : E)) :
    let τk : ℝ := α (k + 1) / A_k α (k + 1)
    let γk : ℝ := (σ / L) * α (k + 1)
    let xhat : E :=
      V_Q Q d (z_k Q f d L σ α xSeq k) (γk • fderiv ℝ f (xSeq (k + 1)))
    (ySeq (k + 1) : E) - (xSeq (k + 1) : E) =
      τk • (xhat - (z_k Q f d L σ α xSeq k : E)) := by
  classical
  let τk : ℝ := α (k + 1) / A_k α (k + 1)
  let γk : ℝ := (σ / L) * α (k + 1)
  let xhat : E :=
    V_Q Q d (z_k Q f d L σ α xSeq k) (γk • fderiv ℝ f (xSeq (k + 1)))
  have hy :
      (ySeq (k + 1) : E) = τk • xhat + (1 - τk) • (ySeq k : E) := by
    simpa [τk, γk, xhat] using hy_update
  have hx :
      (xSeq (k + 1) : E) =
        τk • (z_k Q f d L σ α xSeq k : E) + (1 - τk) • (ySeq k : E) := by
    simpa [τk] using hx_update
  calc
    (ySeq (k + 1) : E) - (xSeq (k + 1) : E) =
        (τk • xhat + (1 - τk) • (ySeq k : E)) -
          (τk • (z_k Q f d L σ α xSeq k : E) + (1 - τk) • (ySeq k : E)) := by
      simp [hy, hx]
    _ = τk • (xhat - (z_k Q f d L σ α xSeq k : E)) := by
      simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, smul_add]

/-- Final convexity step for the modified invariant update. -/
lemma section05_final_convexity_step {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {Q : Set E} {f : E → ℝ} (xSeq ySeq : ℕ → Q) (k : ℕ)
    (hQ_convex : Convex ℝ Q) (hf_convex : ConvexOn ℝ Q f)
    (hf_diff : ∀ x ∈ Q, DifferentiableAt ℝ f x) :
    let xk1 : E := xSeq (k + 1)
    let g : Module.Dual ℝ E := (fderiv ℝ f (xSeq (k + 1))).toLinearMap
    f (ySeq (k + 1)) ≥ f xk1 + DualPairing g ((ySeq (k + 1) : E) - xk1) := by
  classical
  let xk1 : E := xSeq (k + 1)
  let g : Module.Dual ℝ E := (fderiv ℝ f (xSeq (k + 1))).toLinearMap
  have hxk1 : (xSeq (k + 1) : E) ∈ Q := (xSeq (k + 1)).property
  have hyk1 : (ySeq (k + 1) : E) ∈ Q := (ySeq (k + 1)).property
  have hsupport :
      f (ySeq (k + 1)) ≥ f xk1 + DualPairing g ((ySeq (k + 1) : E) - xk1) := by
    exact
      section03_convex_support_fderiv (hQ_convex := hQ_convex) (hf_convex := hf_convex)
        (u := (ySeq (k + 1) : E)) (v := (xSeq (k + 1) : E)) hyk1 hxk1
        (hf_diff (xSeq (k + 1)) hxk1)
  simpa [xk1, g] using hsupport

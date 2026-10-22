/-
Authors: Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Papers/SmoothMinimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib
import Papers.SmoothMinimization_Nesterov_2004.section04_part4

/-- The softmax vector belongs to the standard simplex (and its normalizer is positive). -/
lemma entropySimplex_softmax_den_pos_and_mem (m : ℕ) (μ : ℝ) (s : Fin m → ℝ) (hm : 0 < m) :
    let Z : ℝ := ∑ j : Fin m, Real.exp (s j / μ)
    0 < Z ∧ (fun j : Fin m => Real.exp (s j / μ) / Z) ∈ standardSimplex m := by
  classical
  dsimp
  set Z : ℝ := ∑ j : Fin m, Real.exp (s j / μ) with hZ
  have hZpos : 0 < Z := by
    simpa [hZ] using entropySimplex_softmax_den_pos (m := m) (μ := μ) (s := s) hm
  have hZne : Z ≠ 0 := ne_of_gt hZpos
  refine ⟨hZpos, ?_⟩
  refine ⟨?_, ?_⟩
  · intro j
    have : 0 < Real.exp (s j / μ) / Z := div_pos (Real.exp_pos (s j / μ)) hZpos
    exact le_of_lt (by simpa [hZ] using this)
  · have hsum_div :
        (∑ j : Fin m, Real.exp (s j / μ) / Z) =
          (∑ j : Fin m, Real.exp (s j / μ)) / Z := by
      simpa using
        (Finset.sum_div (s := (Finset.univ : Finset (Fin m)))
          (f := fun j => Real.exp (s j / μ)) (a := Z)).symm
    calc
      (∑ j : Fin m, Real.exp (s j / μ) / Z)
          = (∑ j : Fin m, Real.exp (s j / μ)) / Z := hsum_div
      _ = Z / Z := by simp [hZ]
      _ = (1 : ℝ) := by simp [hZne]

/-- Scalar inequality underlying KL nonnegativity: `v * log(v/u) ≥ v - u` for `u > 0`, `v ≥ 0`. -/
lemma entropySimplex_mul_log_div_ge_sub {u v : ℝ} (hu : 0 < u) (hv : 0 ≤ v) :
    v * Real.log (v / u) ≥ v - u := by
  by_cases hv0 : v = 0
  · subst hv0
    simp [hu.le]
  · have hvpos : 0 < v := lt_of_le_of_ne hv (Ne.symm hv0)
    have hx : 0 < u / v := div_pos hu hvpos
    have hlog : Real.log (u / v) ≤ u / v - 1 := Real.log_le_sub_one_of_pos hx
    have hv' : 0 < v := hvpos
    have hmul : v * Real.log (u / v) ≤ v * (u / v - 1) := by
      exact mul_le_mul_of_nonneg_left hlog (le_of_lt hv')
    have hmul' : v * (u / v - 1) = u - v := by
      calc
        v * (u / v - 1) = v * (u / v) - v := by ring
        _ = u - v := by simp [mul_div_cancel₀ u hv0]
    have hbase : -(v * Real.log (u / v)) ≥ v - u := by
      have : v * Real.log (u / v) ≤ u - v := by simpa [hmul'] using hmul
      linarith
    -- rewrite `-log(u/v)` as `log(v/u)`
    have hloginv : Real.log (v / u) = -Real.log (u / v) := by
      simpa [inv_div] using (Real.log_inv (u / v))
    -- finalize
    have : v * Real.log (v / u) = -(v * Real.log (u / v)) := by
      calc
        v * Real.log (v / u) = v * (-Real.log (u / v)) := by simp [hloginv]
        _ = -(v * Real.log (u / v)) := by ring
    simpa [this] using hbase

/-- Rewrite `v * log(v/u)` as `v * log v - v * log u` (handles `v = 0` by cases). -/
lemma entropySimplex_mul_log_div_eq (u v : ℝ) (hu : u ≠ 0) :
    v * Real.log (v / u) = v * Real.log v - v * Real.log u := by
  by_cases hv0 : v = 0
  · subst hv0
    simp
  · have hv : v ≠ 0 := hv0
    simp [Real.log_div hv hu, mul_sub]

/-- Nonnegativity of the KL divergence `∑ v_j log(v_j/u_j)` on the simplex against a positive `u`. -/
lemma entropySimplex_KL_nonneg {m : ℕ} {v u : Fin m → ℝ}
    (hv : v ∈ standardSimplex m) (hu_pos : ∀ j, 0 < u j) (hu_sum : ∑ j, u j = (1 : ℝ)) :
    0 ≤ ∑ j : Fin m, v j * Real.log (v j / u j) := by
  classical
  have hv_nonneg : ∀ j, 0 ≤ v j := hv.1
  have hv_sum : ∑ j, v j = (1 : ℝ) := hv.2
  have hterm :
      ∀ j : Fin m, v j - u j ≤ v j * Real.log (v j / u j) := by
    intro j
    have := entropySimplex_mul_log_div_ge_sub (u := u j) (v := v j) (hu := hu_pos j) (hv := hv_nonneg j)
    linarith
  have hsum :
      (∑ j : Fin m, (v j - u j)) ≤ ∑ j : Fin m, v j * Real.log (v j / u j) := by
    have :
        (Finset.univ.sum fun j : Fin m => v j - u j) ≤
          (Finset.univ.sum fun j : Fin m => v j * Real.log (v j / u j)) := by
      refine Finset.sum_le_sum ?_
      intro j hj
      exact hterm j
    simpa using this
  have hleft0 : (∑ j : Fin m, (v j - u j)) = 0 := by
    have hsub :
        (∑ j : Fin m, (v j - u j)) = (∑ j : Fin m, v j) - (∑ j : Fin m, u j) := by
      simp [Finset.sum_sub_distrib]
    calc
      (∑ j : Fin m, (v j - u j)) = (∑ j : Fin m, v j) - (∑ j : Fin m, u j) := hsub
      _ = (1 : ℝ) - (1 : ℝ) := by simp [hv_sum, hu_sum]
      _ = 0 := by ring
  simpa [hleft0] using hsum

/-- The entropy-regularized objective at the softmax point equals `μ * log(∑ exp(s/μ))`. -/
lemma entropySimplex_obj_at_softmax (m : ℕ) (μ : ℝ) (s : Fin m → ℝ) (hm : 0 < m) (hμ : 0 < μ) :
    let Z : ℝ := ∑ j : Fin m, Real.exp (s j / μ)
    let uμ : Fin m → ℝ := fun j => Real.exp (s j / μ) / Z
    (∑ j, uμ j * s j) - μ * (∑ j, uμ j * Real.log (uμ j)) = μ * Real.log Z := by
  classical
  dsimp
  set Z : ℝ := ∑ j : Fin m, Real.exp (s j / μ) with hZ
  set uμ : Fin m → ℝ := fun j => Real.exp (s j / μ) / Z with huμ
  have hZpos : 0 < Z := by
    simpa [hZ] using entropySimplex_softmax_den_pos (m := m) (μ := μ) (s := s) hm
  have hZne : Z ≠ 0 := ne_of_gt hZpos
  have hu_mem : uμ ∈ standardSimplex m := by
    have h := entropySimplex_softmax_den_pos_and_mem (m := m) (μ := μ) (s := s) hm
    simpa [hZ, huμ] using h.2
  have hu_sum : ∑ j : Fin m, uμ j = (1 : ℝ) := hu_mem.2
  have hμne : μ ≠ 0 := ne_of_gt hμ
  have hlog_u : ∀ j : Fin m, Real.log (uμ j) = s j / μ - Real.log Z := by
    intro j
    have hexp : Real.exp (s j / μ) ≠ 0 := Real.exp_ne_zero (s j / μ)
    simp [huμ, Real.log_div hexp hZne, Real.log_exp, sub_eq_add_neg]
  have hsum_log :
      (∑ j : Fin m, uμ j * Real.log (uμ j)) =
        (∑ j : Fin m, uμ j * (s j / μ)) - Real.log Z := by
    calc
      (∑ j : Fin m, uμ j * Real.log (uμ j)) =
          ∑ j : Fin m, uμ j * (s j / μ - Real.log Z) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            simp [hlog_u j]
      _ = ∑ j : Fin m, (uμ j * (s j / μ) - uμ j * Real.log Z) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            ring
      _ = (∑ j : Fin m, uμ j * (s j / μ)) - (∑ j : Fin m, uμ j * Real.log Z) := by
            simp [Finset.sum_sub_distrib]
      _ = (∑ j : Fin m, uμ j * (s j / μ)) - (Real.log Z * (∑ j : Fin m, uμ j)) := by
            congr 1
            calc
              (∑ j : Fin m, uμ j * Real.log Z) = ∑ j : Fin m, (Real.log Z) * uμ j := by
                  refine Finset.sum_congr rfl ?_
                  intro j hj
                  ring
              _ = (Real.log Z) * (∑ j : Fin m, uμ j) := by simp [Finset.mul_sum]
      _ = (∑ j : Fin m, uμ j * (s j / μ)) - Real.log Z := by simp [hu_sum]
  have hmu_cancel :
      μ * (∑ j : Fin m, uμ j * (s j / μ)) = ∑ j : Fin m, uμ j * s j := by
    calc
      μ * (∑ j : Fin m, uμ j * (s j / μ)) =
          ∑ j : Fin m, μ * (uμ j * (s j / μ)) := by simp [Finset.mul_sum]
      _ = ∑ j : Fin m, uμ j * s j := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          calc
            μ * (uμ j * (s j / μ)) = uμ j * (μ * (s j / μ)) := by ring
            _ = uμ j * s j := by simp [mul_div_cancel₀ (s j) hμne]
  calc
    (∑ j : Fin m, uμ j * s j) - μ * (∑ j : Fin m, uμ j * Real.log (uμ j))
        = (∑ j : Fin m, uμ j * s j) - μ * ((∑ j : Fin m, uμ j * (s j / μ)) - Real.log Z) := by
            simp [hsum_log]
    _ = (∑ j : Fin m, uμ j * s j) - μ * (∑ j : Fin m, uμ j * (s j / μ)) + μ * Real.log Z := by
            ring
    _ = μ * Real.log Z := by
            -- the linear term cancels with the entropy term using `μ ≠ 0`
            simp [hmu_cancel]

/-- Any point of the simplex achieves objective value at most the softmax value `μ * log(∑ exp(s/μ))`. -/
lemma entropySimplex_obj_le_softmax (m : ℕ) (μ : ℝ) (s : Fin m → ℝ) (hm : 0 < m) (hμ : 0 < μ) :
    let Z : ℝ := ∑ j : Fin m, Real.exp (s j / μ)
    let _uμ : Fin m → ℝ := fun j => Real.exp (s j / μ) / Z
    ∀ v ∈ standardSimplex m,
      (∑ j, v j * s j) - μ * (∑ j, v j * Real.log (v j)) ≤ μ * Real.log Z := by
  classical
  dsimp
  set Z : ℝ := ∑ j : Fin m, Real.exp (s j / μ) with hZ
  set uμ : Fin m → ℝ := fun j => Real.exp (s j / μ) / Z with huμ
  have hZpos : 0 < Z := by
    simpa [hZ] using entropySimplex_softmax_den_pos (m := m) (μ := μ) (s := s) hm
  have hZne : Z ≠ 0 := ne_of_gt hZpos
  have hu_mem : uμ ∈ standardSimplex m := by
    have h := entropySimplex_softmax_den_pos_and_mem (m := m) (μ := μ) (s := s) hm
    simpa [hZ, huμ] using h.2
  have hu_sum : ∑ j : Fin m, uμ j = (1 : ℝ) := hu_mem.2
  have hu_pos : ∀ j : Fin m, 0 < uμ j := by
    intro j
    have : 0 < Real.exp (s j / μ) / Z := div_pos (Real.exp_pos (s j / μ)) hZpos
    simpa [huμ] using this
  have hμne : μ ≠ 0 := ne_of_gt hμ
  have hlog_u : ∀ j : Fin m, Real.log (uμ j) = s j / μ - Real.log Z := by
    intro j
    have hexp : Real.exp (s j / μ) ≠ 0 := Real.exp_ne_zero (s j / μ)
    simp [huμ, Real.log_div hexp hZne, Real.log_exp, sub_eq_add_neg]
  have hs_div : ∀ j : Fin m, s j / μ = Real.log (uμ j) + Real.log Z := by
    intro j
    have := hlog_u j
    linarith
  intro v hv
  have hv_sum : ∑ j : Fin m, v j = (1 : ℝ) := hv.2
  have hlin :
      (∑ j : Fin m, v j * s j) = μ * (∑ j : Fin m, v j * (s j / μ)) := by
    calc
      (∑ j : Fin m, v j * s j) = ∑ j : Fin m, v j * (μ * (s j / μ)) := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        simp [mul_div_cancel₀ (s j) hμne, mul_comm]
      _ = ∑ j : Fin m, μ * (v j * (s j / μ)) := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        ring
      _ = μ * (∑ j : Fin m, v j * (s j / μ)) := by simp [Finset.mul_sum]
  have hsum_sdiv :
      (∑ j : Fin m, v j * (s j / μ)) =
        (∑ j : Fin m, v j * Real.log (uμ j)) + Real.log Z := by
    calc
      (∑ j : Fin m, v j * (s j / μ)) =
          ∑ j : Fin m, v j * (Real.log (uμ j) + Real.log Z) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            simp [hs_div j]
      _ = ∑ j : Fin m, (v j * Real.log (uμ j) + v j * Real.log Z) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            ring
      _ =
          (∑ j : Fin m, v j * Real.log (uμ j)) + (∑ j : Fin m, v j * Real.log Z) := by
            simp [Finset.sum_add_distrib]
      _ = (∑ j : Fin m, v j * Real.log (uμ j)) + (Real.log Z * (∑ j : Fin m, v j)) := by
            congr 1
            calc
              (∑ j : Fin m, v j * Real.log Z) = ∑ j : Fin m, (Real.log Z) * v j := by
                  refine Finset.sum_congr rfl ?_
                  intro j hj
                  ring
              _ = (Real.log Z) * (∑ j : Fin m, v j) := by simp [Finset.mul_sum]
      _ = (∑ j : Fin m, v j * Real.log (uμ j)) + Real.log Z := by simp [hv_sum]
  have hsum_logdiv :
      (∑ j : Fin m, v j * Real.log (v j / uμ j)) =
        (∑ j : Fin m, v j * Real.log (v j)) - (∑ j : Fin m, v j * Real.log (uμ j)) := by
    calc
      (∑ j : Fin m, v j * Real.log (v j / uμ j)) =
          ∑ j : Fin m, (v j * Real.log (v j) - v j * Real.log (uμ j)) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            have huj : uμ j ≠ 0 := ne_of_gt (hu_pos j)
            simp [entropySimplex_mul_log_div_eq (u := uμ j) (v := v j) huj]
      _ =
          (∑ j : Fin m, v j * Real.log (v j)) - (∑ j : Fin m, v j * Real.log (uμ j)) := by
            simp [Finset.sum_sub_distrib]
  have hkl : 0 ≤ ∑ j : Fin m, v j * Real.log (v j / uμ j) := by
    exact entropySimplex_KL_nonneg (hv := hv) (hu_pos := hu_pos) (hu_sum := hu_sum)
  have hdiff :
      0 ≤ μ * Real.log Z -
          ((∑ j : Fin m, v j * s j) - μ * (∑ j : Fin m, v j * Real.log (v j))) := by
    have :
        μ * Real.log Z -
              ((∑ j : Fin m, v j * s j) - μ * (∑ j : Fin m, v j * Real.log (v j))) =
            μ * (∑ j : Fin m, v j * Real.log (v j / uμ j)) := by
      calc
        μ * Real.log Z -
              ((∑ j : Fin m, v j * s j) - μ * (∑ j : Fin m, v j * Real.log (v j))) =
            μ * Real.log Z - (∑ j : Fin m, v j * s j) + μ * (∑ j : Fin m, v j * Real.log (v j)) := by
              ring
        _ =
            μ * Real.log Z - μ * (∑ j : Fin m, v j * (s j / μ)) + μ * (∑ j : Fin m, v j * Real.log (v j)) := by
              simp [hlin]
        _ = μ * (Real.log Z - (∑ j : Fin m, v j * (s j / μ)) + (∑ j : Fin m, v j * Real.log (v j))) := by
              ring
        _ = μ * ((∑ j : Fin m, v j * Real.log (v j)) - (∑ j : Fin m, v j * Real.log (uμ j))) := by
              congr 1
              simp [hsum_sdiv]
              ring
        _ = μ * (∑ j : Fin m, v j * Real.log (v j / uμ j)) := by
              simp [hsum_logdiv]
    have hdiff_nonneg : 0 ≤ μ * (∑ j : Fin m, v j * Real.log (v j / uμ j)) :=
      mul_nonneg (le_of_lt hμ) hkl
    simpa [this] using hdiff_nonneg
  exact (sub_nonneg.mp hdiff)

/-- Lemma 1.4.1.2.
For `μ > 0` and `s ∈ ℝ^m`, define
`Φ_μ(s) = max_{u ∈ Δ_m} {∑ u^{(j)} s^{(j)} - μ ∑ u^{(j)} ln u^{(j)}}` (4.13).
The maximizer `u_μ(s)` has entries
`u_μ^{(j)}(s) = exp(s^{(j)}/μ) / ∑_l exp(s^{(l)}/μ)` (4.14), and
`Φ_μ(s) = μ ln(∑_j exp(s^{(j)}/μ))`. -/
theorem entropySimplex_softmax_maximizer (m : ℕ) (μ : ℝ) (s : Fin m → ℝ) (hm : 0 < m)
    (hμ : 0 < μ) :
    let Φμ : ℝ :=
      sSup
        ((fun u =>
            (∑ j, u j * s j) - μ * (∑ j, u j * Real.log (u j))) '' standardSimplex m)
    let uμ : Fin m → ℝ :=
      fun j => Real.exp (s j / μ) / (∑ l, Real.exp (s l / μ))
    uμ ∈ standardSimplex m ∧
      (∀ v ∈ standardSimplex m,
        (∑ j, v j * s j) - μ * (∑ j, v j * Real.log (v j)) ≤
          (∑ j, uμ j * s j) - μ * (∑ j, uμ j * Real.log (uμ j))) ∧
      Φμ = μ * Real.log (∑ j, Real.exp (s j / μ)) := by
  classical
  dsimp
  set Z : ℝ := ∑ j : Fin m, Real.exp (s j / μ) with hZ
  set uμ : Fin m → ℝ := fun j => Real.exp (s j / μ) / Z with huμ
  have hZpos : 0 < Z := by
    simpa [hZ] using entropySimplex_softmax_den_pos (m := m) (μ := μ) (s := s) hm
  have hu_mem : uμ ∈ standardSimplex m := by
    have h := entropySimplex_softmax_den_pos_and_mem (m := m) (μ := μ) (s := s) hm
    simpa [hZ, huμ] using h.2
  have hu_obj :
      (∑ j : Fin m, uμ j * s j) - μ * (∑ j : Fin m, uμ j * Real.log (uμ j)) = μ * Real.log Z := by
    have h := entropySimplex_obj_at_softmax (m := m) (μ := μ) (s := s) hm hμ
    simpa [hZ, huμ] using h
  have hupper :
      ∀ v ∈ standardSimplex m,
        (∑ j : Fin m, v j * s j) - μ * (∑ j : Fin m, v j * Real.log (v j)) ≤
          (∑ j : Fin m, uμ j * s j) - μ * (∑ j : Fin m, uμ j * Real.log (uμ j)) := by
    intro v hv
    have hv_le : (∑ j : Fin m, v j * s j) - μ * (∑ j : Fin m, v j * Real.log (v j)) ≤ μ * Real.log Z := by
      have h := entropySimplex_obj_le_softmax (m := m) (μ := μ) (s := s) hm hμ
      simpa [hZ, huμ] using h v hv
    -- rewrite the softmax objective as `μ * log Z`
    simpa [hu_obj] using hv_le
  refine ⟨by simpa [huμ, hZ] using hu_mem, hupper, ?_⟩
  -- identify the supremum with the objective value at `uμ`
  set S : Set ℝ :=
      ((fun u : Fin m → ℝ =>
          (∑ j : Fin m, u j * s j) - μ * (∑ j : Fin m, u j * Real.log (u j))) '' standardSimplex m) with
    hS
  have hS_nonempty : S.Nonempty := by
    refine ⟨(∑ j : Fin m, uμ j * s j) - μ * (∑ j : Fin m, uμ j * Real.log (uμ j)), ?_⟩
    refine ⟨uμ, ?_, rfl⟩
    simpa [hS] using hu_mem
  have hS_bdd : BddAbove S := by
    refine ⟨(∑ j : Fin m, uμ j * s j) - μ * (∑ j : Fin m, uμ j * Real.log (uμ j)), ?_⟩
    intro y hy
    rcases hy with ⟨v, hv, rfl⟩
    exact hupper v hv
  have hsSup_eq :
      sSup S =
        (∑ j : Fin m, uμ j * s j) - μ * (∑ j : Fin m, uμ j * Real.log (uμ j)) := by
    refine le_antisymm ?_ ?_
    · -- `sSup S ≤ obj(uμ)` since `obj(uμ)` is an upper bound on the image
      refine csSup_le hS_nonempty ?_
      intro y hy
      rcases hy with ⟨v, hv, rfl⟩
      exact hupper v hv
    · -- `obj(uμ) ≤ sSup S` since `obj(uμ) ∈ S`
      refine le_csSup hS_bdd ?_
      refine ⟨uμ, ?_, rfl⟩
      simpa [hS] using hu_mem
  -- finish by evaluating at the softmax point
  have : sSup S = μ * Real.log Z := by simp [hsSup_eq, hu_obj]
  simpa [hS, hZ] using this

/-- Evaluate a continuous linear functional `ℓ : (Fin m → ℝ) →L[ℝ] ℝ` as a coordinate sum against
the standard basis vectors `e_j(k) = if k = j then 1 else 0`. -/
lemma matrixGame_contLin_apply_eq_sum_basis (m : ℕ)
    (ℓ : (Fin m → ℝ) →L[ℝ] ℝ) (u : Fin m → ℝ) :
    ℓ u =
      ∑ j : Fin m, u j * ℓ (fun k : Fin m => if k = j then (1 : ℝ) else 0) := by
  classical
  have hu :
      u = ∑ j : Fin m, u j • (fun k : Fin m => if k = j then (1 : ℝ) else 0) := by
    -- `pi_eq_sum_univ` uses the basis `fun k => if j = k then 1 else 0`; rewrite using `eq_comm`.
    simpa [eq_comm] using (pi_eq_sum_univ (x := u) (R := ℝ))
  -- rewrite `u`, then push `ℓ` through the sum and scalars
  rw [hu]
  -- use `map_sum` for additive monoid homs
  have hmap :=
    (map_sum ℓ (fun j : Fin m => u j • (fun k : Fin m => if k = j then (1 : ℝ) else 0))
      (Finset.univ : Finset (Fin m)))
  -- clean up the `∑ x ∈ univ` binders and rewrite `•` as multiplication on `ℝ`
  simp [hmap, smul_eq_mul]

/-- On the standard simplex `Δ_m`, rewrite the smoothed matrix-game integrand as the entropy
objective `∑ u_j s_j - μ ∑ u_j log u_j` with
`s_j = ℓ(e_j) + b_j - μ log m`, absorbing the constant term via `∑ u_j = 1`. -/
lemma matrixGame_entropy_objective_rewrite (m : ℕ) (μ : ℝ)
    (ℓ : (Fin m → ℝ) →L[ℝ] ℝ) (b : Fin m → ℝ) (u : Fin m → ℝ)
    (hu : u ∈ standardSimplex m) :
    (ℓ u + (∑ j : Fin m, b j * u j) - μ * (Real.log (m : ℝ) + ∑ j : Fin m, u j * Real.log (u j))) =
      (∑ j : Fin m,
          u j *
            (ℓ (fun k : Fin m => if k = j then (1 : ℝ) else 0) + b j - μ * Real.log (m : ℝ))) -
        μ * (∑ j : Fin m, u j * Real.log (u j)) := by
  classical
  have hℓ :
      ℓ u = ∑ j : Fin m, u j * ℓ (fun k : Fin m => if k = j then (1 : ℝ) else 0) := by
    simpa using matrixGame_contLin_apply_eq_sum_basis (m := m) (ℓ := ℓ) (u := u)
  have hu_sum : (∑ j : Fin m, u j) = (1 : ℝ) := hu.2
  have hbu : (∑ j : Fin m, b j * u j) = ∑ j : Fin m, u j * b j := by
    simp [mul_comm]
  have hconst : (∑ j : Fin m, u j * (μ * Real.log (m : ℝ))) = μ * Real.log (m : ℝ) := by
    calc
      (∑ j : Fin m, u j * (μ * Real.log (m : ℝ))) =
          ∑ j : Fin m, (μ * Real.log (m : ℝ)) * u j := by
            simp [mul_comm]
      _ = (μ * Real.log (m : ℝ)) * (∑ j : Fin m, u j) := by
            simp [Finset.mul_sum]
      _ = μ * Real.log (m : ℝ) := by simp [hu_sum]
  have hsum :
      (∑ j : Fin m,
          u j *
            (ℓ (fun k : Fin m => if k = j then (1 : ℝ) else 0) + b j - μ * Real.log (m : ℝ))) =
        (∑ j : Fin m, u j * ℓ (fun k : Fin m => if k = j then (1 : ℝ) else 0)) +
          (∑ j : Fin m, u j * b j) - μ * Real.log (m : ℝ) := by
    calc
      (∑ j : Fin m,
          u j *
            (ℓ (fun k : Fin m => if k = j then (1 : ℝ) else 0) + b j - μ * Real.log (m : ℝ))) =
          ∑ j : Fin m,
            (u j * ℓ (fun k : Fin m => if k = j then (1 : ℝ) else 0) + u j * b j -
              u j * (μ * Real.log (m : ℝ))) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            ring
      _ =
          (∑ j : Fin m, u j * ℓ (fun k : Fin m => if k = j then (1 : ℝ) else 0)) +
              (∑ j : Fin m, u j * b j) -
            (∑ j : Fin m, u j * (μ * Real.log (m : ℝ))) := by
            simp [Finset.sum_add_distrib, sub_eq_add_neg, add_left_comm, add_comm]
      _ =
          (∑ j : Fin m, u j * ℓ (fun k : Fin m => if k = j then (1 : ℝ) else 0)) +
              (∑ j : Fin m, u j * b j) -
            μ * Real.log (m : ℝ) := by
            simp [hconst]
  -- rewrite the linear terms and expand `-μ * (log m + ...)`
  calc
    (ℓ u + (∑ j : Fin m, b j * u j) - μ * (Real.log (m : ℝ) + ∑ j : Fin m, u j * Real.log (u j))) =
        (∑ j : Fin m, u j * ℓ (fun k : Fin m => if k = j then (1 : ℝ) else 0)) +
          (∑ j : Fin m, u j * b j) - μ * Real.log (m : ℝ) -
            μ * (∑ j : Fin m, u j * Real.log (u j)) := by
          simp [hℓ, hbu, mul_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    _ =
        (∑ j : Fin m,
            u j *
              (ℓ (fun k : Fin m => if k = j then (1 : ℝ) else 0) + b j - μ * Real.log (m : ℝ))) -
          μ * (∑ j : Fin m, u j * Real.log (u j)) := by
          -- use `hsum` to compress the linear part
          have hsum' :
              (∑ j : Fin m, u j * ℓ (fun k : Fin m => if k = j then (1 : ℝ) else 0)) +
                  (∑ j : Fin m, u j * b j) - μ * Real.log (m : ℝ) =
                ∑ j : Fin m,
                  u j *
                    (ℓ (fun k : Fin m => if k = j then (1 : ℝ) else 0) + b j -
                      μ * Real.log (m : ℝ)) := by
            simpa using hsum.symm
          -- rewrite the linear part using `hsum'`
          simpa using
            congrArg (fun z =>
              z - μ * (∑ j : Fin m, u j * Real.log (u j))) hsum'

/-- Rewrite the log-sum-exp shift
`∑ exp((t_j - μ log m)/μ) = (1/m) * ∑ exp(t_j/μ)` for `m > 0` and `μ ≠ 0`. -/
lemma matrixGame_logsumexp_shift_by_log_m (m : ℕ) (μ : ℝ) (t : Fin m → ℝ)
    (hm : 0 < m) (hμ : μ ≠ 0) :
    (∑ j : Fin m, Real.exp ((t j - μ * Real.log (m : ℝ)) / μ)) =
      (1 / (m : ℝ)) * ∑ j : Fin m, Real.exp (t j / μ) := by
  classical
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hdiv : ∀ j : Fin m, (t j - μ * Real.log (m : ℝ)) / μ = t j / μ - Real.log (m : ℝ) := by
    intro j
    calc
      (t j - μ * Real.log (m : ℝ)) / μ = t j / μ - (μ * Real.log (m : ℝ)) / μ := by
        simp [sub_div]
      _ = t j / μ - Real.log (m : ℝ) := by
        simp [mul_div_cancel_left₀ (b := Real.log (m : ℝ)) hμ]
  calc
    (∑ j : Fin m, Real.exp ((t j - μ * Real.log (m : ℝ)) / μ)) =
        ∑ j : Fin m, Real.exp (t j / μ - Real.log (m : ℝ)) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          simp [hdiv j]
    _ = ∑ j : Fin m, Real.exp (t j / μ) / (m : ℝ) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          have : Real.exp (Real.log (m : ℝ)) = (m : ℝ) := by simpa using (Real.exp_log hmR)
          simp [Real.exp_sub, this]
    _ = (∑ j : Fin m, Real.exp (t j / μ)) / (m : ℝ) := by
          simpa using
            (Finset.sum_div (s := (Finset.univ : Finset (Fin m)))
              (f := fun j : Fin m => Real.exp (t j / μ)) (a := (m : ℝ))).symm
    _ = (1 / (m : ℝ)) * ∑ j : Fin m, Real.exp (t j / μ) := by
          simp [div_eq_mul_inv, mul_comm]

/-- Proposition 1.4.1.3.
In the matrix-game setting (4.10), under the entropy-distance setup of Lemma 1.4.1.2, the
smoothed objective (4.1) for the primal problem is
`\bar f_μ(x) = ⟪c,x⟫_1 + μ ln((1/m) ∑_{j=1}^m exp((⟪a_j,x⟫_1 + b^{(j)})/μ))`, with the
minimization `min_{x ∈ Δ_n} \bar f_μ(x)` (eq:matrixgame_smooth). -/
theorem matrixGame_smoothedObjective_explicit (n m : ℕ)
    (A : (Fin n → ℝ) →L[ℝ] ((Fin m → ℝ) →L[ℝ] ℝ)) (c : Fin n → ℝ) (b : Fin m → ℝ) (μ : ℝ)
    (hμ : 0 < μ) :
    let fhat : (Fin n → ℝ) → ℝ := fun x => ∑ i, c i * x i
    let phihat : (Fin m → ℝ) → ℝ := fun u => -∑ j, b j * u j
    let d2 : (Fin m → ℝ) → ℝ :=
      fun u => Real.log (m : ℝ) + ∑ j, u j * Real.log (u j)
    let fbar : (Fin n → ℝ) → ℝ := SmoothedObjective (standardSimplex m) A phihat d2 μ fhat
    fbar =
      fun x =>
        (∑ i, c i * x i) +
          μ * Real.log ((1 / (m : ℝ)) *
            ∑ j,
              Real.exp (((A x) (fun k => if k = j then (1 : ℝ) else 0) + b j) / μ)) := by
  classical
  funext x
  by_cases hm0 : m = 0
  · subst hm0
    -- `Δ_0` is empty, so the smoothed max-term is `sSup ∅ = 0`, and the RHS sum is empty.
    have hsimplex0 : (standardSimplex 0 : Set (Fin 0 → ℝ)) = ∅ := by
      ext u
      simp [standardSimplex]
    simp [SmoothedObjective, SmoothedMaxFunction, Real.sSup_empty, standardSimplex]
  · have hm : 0 < m := Nat.pos_of_ne_zero hm0
    have hμne : μ ≠ 0 := ne_of_gt hμ
    -- Evaluate the `sSup` in the smoothed max-function via the entropy simplex lemma.
    have hmax :
        SmoothedMaxFunction (standardSimplex m) A (fun u => -∑ j : Fin m, b j * u j)
            (fun u : Fin m → ℝ => Real.log (m : ℝ) + ∑ j : Fin m, u j * Real.log (u j)) μ x =
          μ * Real.log
            ((1 / (m : ℝ)) *
              ∑ j : Fin m,
                Real.exp (((A x) (fun k : Fin m => if k = j then (1 : ℝ) else 0) + b j) / μ)) := by
      set t : Fin m → ℝ :=
          fun j : Fin m => (A x) (fun k : Fin m => if k = j then (1 : ℝ) else 0) + b j with ht
      set s : Fin m → ℝ := fun j : Fin m => t j - μ * Real.log (m : ℝ) with hs
      have himage :
          ((fun u : Fin m → ℝ =>
                A x u + (∑ j : Fin m, b j * u j) -
                    μ * (Real.log (m : ℝ) + ∑ j : Fin m, u j * Real.log (u j))) '' standardSimplex m) =
            ((fun u : Fin m → ℝ =>
                  (∑ j : Fin m, u j * s j) - μ * (∑ j : Fin m, u j * Real.log (u j))) ''
              standardSimplex m) := by
        refine Set.image_congr ?_
        intro u hu
        have hrewrite :=
          matrixGame_entropy_objective_rewrite (m := m) (μ := μ) (ℓ := (A x)) (b := b) (u := u) hu
        have hs' : ∀ j : Fin m,
            s j = (A x) (fun k : Fin m => if k = j then (1 : ℝ) else 0) + b j - μ * Real.log (m : ℝ) := by
          intro j
          simp [s, t, sub_eq_add_neg, add_left_comm, add_comm]
        simpa [hs', sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hrewrite
      have hentropy :
          sSup
              (((fun u : Fin m → ℝ =>
                      (∑ j : Fin m, u j * s j) - μ * (∑ j : Fin m, u j * Real.log (u j))) ''
                  standardSimplex m)) =
            μ * Real.log (∑ j : Fin m, Real.exp (s j / μ)) := by
        have h := entropySimplex_softmax_maximizer (m := m) (μ := μ) (s := s) hm hμ
        simpa using h.2.2
      have hshift :
          (∑ j : Fin m, Real.exp (s j / μ)) =
            (1 / (m : ℝ)) * ∑ j : Fin m,
              Real.exp (((A x) (fun k : Fin m => if k = j then (1 : ℝ) else 0) + b j) / μ) := by
        have hterm :
            (∑ j : Fin m, Real.exp (s j / μ)) =
              (1 / (m : ℝ)) * ∑ j : Fin m, Real.exp (t j / μ) := by
          have : (∑ j : Fin m, Real.exp (s j / μ)) =
              (∑ j : Fin m, Real.exp ((t j - μ * Real.log (m : ℝ)) / μ)) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            simp [s]
          -- apply the shift lemma and rewrite `t`
          simpa [this, div_eq_mul_inv, one_div, mul_assoc, mul_left_comm, mul_comm] using
            (matrixGame_logsumexp_shift_by_log_m (m := m) (μ := μ) (t := t) hm hμne)
        -- unfold `t` in the RHS
        simp [t, hterm]
      simp [SmoothedMaxFunction, himage, hentropy, hshift]
    simp [SmoothedObjective, hmax]

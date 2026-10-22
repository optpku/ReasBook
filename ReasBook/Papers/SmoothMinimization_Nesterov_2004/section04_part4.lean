/-
Authors: Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Papers/SmoothMinimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib
import SmoothMinimization_Nesterov_2004.section04_part1
import SmoothMinimization_Nesterov_2004.section04_part3

open scoped NNReal

/-- For any real lower bound `t`, there exists a natural number `N` with `t ≤ (N : ℝ) + 1`. -/
lemma exists_nat_cast_add_one_ge (t : ℝ) : ∃ N : ℕ, t ≤ (N : ℝ) + 1 := by
  refine ⟨Nat.ceil (t - 1), ?_⟩
  have ht : t - 1 ≤ (Nat.ceil (t - 1) : ℝ) := by
    exact Nat.le_ceil (t - 1)
  linarith

/-- Proposition 1.4.2.
In the `M = 0` case of Theorem 1.4.1, an optimal (order-wise) choice of the smoothing parameter `μ`,
the corresponding Lipschitz constant `L_μ`, and the iteration count `N` as a function of accuracy
`ε > 0` is given by
`μ = ε / (2 D2)`, `L_μ = (D2 / (2 σ2)) * (‖A‖_{1,2}^2 / ε)`, and an integer `N` with
`(4 ‖A‖_{1,2} / ε) * sqrt(D1 D2 / (σ1 σ2)) ≤ N + 1` (equation (4.8), up to rounding). -/
theorem optimal_parameters_M_zero {E1 E2 : Type*} [NormedAddCommGroup E1]
    [NormedSpace ℝ E1] [FiniteDimensional ℝ E1] [NormedAddCommGroup E2]
    [NormedSpace ℝ E2] [FiniteDimensional ℝ E2] (Q2 : Set E2)
    (A : E1 →L[ℝ] (E2 →L[ℝ] ℝ)) (d2 : E2 → ℝ) (σ1 σ2 D1 : ℝ) (ε : ℝ) (hε : 0 < ε) :
    let A' : E1 →ₗ[ℝ] Module.Dual ℝ E2 :=
      { toFun := fun x => (A x).toLinearMap
        map_add' := by
          intro x y
          ext u
          simp
        map_smul' := by
          intro c x
          ext u
          simp }
    let D2 : ℝ := sSup (d2 '' Q2)
    ∃ μ Lμ : ℝ, ∃ N : ℕ,
      μ = ε / (2 * D2) ∧
        Lμ = (D2 / (2 * σ2)) * ((OperatorNormDef A') ^ 2 / ε) ∧
          (4 * OperatorNormDef A' / ε) * Real.sqrt (D1 * D2 / (σ1 * σ2)) ≤ (N : ℝ) + 1 := by
  classical
  have _ : ε ≠ 0 := ne_of_gt hε
  dsimp
  set A' : E1 →ₗ[ℝ] Module.Dual ℝ E2 :=
      { toFun := fun x => (A x).toLinearMap
        map_add' := by
          intro x y
          ext u
          simp
        map_smul' := by
          intro c x
          ext u
          simp } with hA'
  set D2 : ℝ := sSup (d2 '' Q2) with hD2
  refine ⟨ε / (2 * D2), (D2 / (2 * σ2)) * ((OperatorNormDef A') ^ 2 / ε), ?_⟩
  rcases
      exists_nat_cast_add_one_ge
        ((4 * OperatorNormDef A' / ε) * Real.sqrt (D1 * D2 / (σ1 * σ2))) with
    ⟨N, hN⟩
  refine ⟨N, rfl, rfl, hN⟩

/-- Definition 1.4.1.1.
The standard simplex `Δ_n` in `ℝ^n` is the set of vectors with nonnegative coordinates summing
to `1` (eq:Delta_n). -/
def standardSimplex (n : ℕ) : Set (Fin n → ℝ) :=
  { x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = (1 : ℝ) }

/-- Definition 1.4.1.1.
The book's standard simplex agrees with mathlib's `stdSimplex` on `Fin n → ℝ`. -/
lemma standardSimplex_eq_stdSimplex (n : ℕ) :
    standardSimplex n = stdSimplex ℝ (Fin n) := by
  rfl

/-- Definition 1.4.1.1.
The matrix-game saddle-point value
`min_{x ∈ Δ_n} max_{u ∈ Δ_m} {⟪A x, u⟫_2 + ⟪c, x⟫_1 + ⟪b, u⟫_2}` (4.9). -/
noncomputable def matrixGameSaddlePointValue (n m : ℕ)
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (c : Fin n → ℝ) (b : Fin m → ℝ) : ℝ :=
  sInf
    ((fun x =>
        sSup
          ((fun u =>
              (∑ i, (A x) i * u i) + (∑ i, c i * x i) + (∑ i, b i * u i)) ''
            standardSimplex m)) ''
      standardSimplex n)

/-- Definition 1.4.1.2.
The primal objective in (4.10): `f(x) = ⟪c,x⟫_1 + max_{1≤j≤m} (⟪a_j,x⟫_1 + b^{(j)})`. -/
noncomputable def matrixGamePrimalObjective (n m : ℕ)
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (c : Fin n → ℝ) (b : Fin m → ℝ) :
    (Fin n → ℝ) → ℝ :=
  fun x =>
    (∑ i, c i * x i) +
      sSup ((fun j => (A x) j + b j) '' (Set.univ : Set (Fin m)))

/-- Definition 1.4.1.2.
The dual objective in (4.10_dual):
`φ(u) = ⟪b,u⟫_2 + min_{1≤i≤n} (⟪\hat a_i,u⟫_2 + c^{(i)})`. -/
noncomputable def matrixGameDualObjective (n m : ℕ)
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (c : Fin n → ℝ) (b : Fin m → ℝ) :
    (Fin m → ℝ) → ℝ :=
  fun u =>
    (∑ j, b j * u j) +
      sInf
        ((fun i =>
            (∑ j, (A (fun k => if k = i then (1 : ℝ) else 0)) j * u j) + c i) ''
          (Set.univ : Set (Fin n)))

/-- The standard basis vector belongs to the standard simplex. -/
lemma standardSimplex_basis_mem (n : ℕ) (i : Fin n) :
    (fun k : Fin n => if k = i then (1 : ℝ) else 0) ∈ standardSimplex n := by
  classical
  refine ⟨?_, ?_⟩
  · intro k
    by_cases hk : k = i
    · simp [hk]
    · simp [hk]
  · simp

/-- The standard simplex is nonempty when `n > 0`. -/
lemma standardSimplex_nonempty_of_pos {n : ℕ} (hn : 0 < n) :
    (standardSimplex n).Nonempty := by
  classical
  refine ⟨_, standardSimplex_basis_mem (n := n) ⟨0, hn⟩⟩

/-- Any linear functional value on the standard simplex is bounded above by the
supremum of its coefficients. -/
lemma linear_standardSimplex_le_sSup_coeff {m : ℕ} (r : Fin m → ℝ) :
    ∀ u ∈ standardSimplex m,
      ∑ i, r i * u i ≤ sSup ((fun i : Fin m => r i) '' (Set.univ : Set (Fin m))) := by
  classical
  intro u hu
  set S : Set ℝ := (fun i : Fin m => r i) '' (Set.univ : Set (Fin m)) with hS
  have hS_bdd : BddAbove S := by
    simp [hS, Set.image_univ]
  have hcoeff : ∀ i, r i ≤ sSup S := by
    intro i
    refine le_csSup hS_bdd ?_
    exact ⟨i, by simp⟩
  have hle : ∑ i, r i * u i ≤ ∑ i, sSup S * u i := by
    refine Finset.sum_le_sum ?_
    intro i hi
    exact mul_le_mul_of_nonneg_right (hcoeff i) (hu.1 i)
  have hsum : ∑ i, sSup S * u i = sSup S := by
    calc
      ∑ i, sSup S * u i = sSup S * ∑ i, u i := by
        symm
        simpa using
          (Finset.mul_sum (s := (Finset.univ : Finset (Fin m))) (a := sSup S)
            (f := fun i => u i))
      _ = sSup S := by
        simp [hu.2]
  exact hle.trans_eq hsum

/-- The supremum of a linear functional over the standard simplex equals the supremum
of its coefficients. -/
lemma sSup_linear_standardSimplex_eq {m : ℕ} (r : Fin m → ℝ) :
    sSup ((fun u : Fin m → ℝ => ∑ i, r i * u i) '' standardSimplex m) =
      sSup ((fun i : Fin m => r i) '' (Set.univ : Set (Fin m))) := by
  classical
  by_cases hm : m = 0
  · subst hm
    simp [standardSimplex]
  · set S : Set ℝ := (fun i : Fin m => r i) '' (Set.univ : Set (Fin m)) with hS
    have hS_bdd : BddAbove S := by
      simp [hS, Set.image_univ]
    have hlinear_le : ∀ u ∈ standardSimplex m, ∑ i, r i * u i ≤ sSup S := by
      intro u hu
      simpa [hS] using (linear_standardSimplex_le_sSup_coeff (r := r) u hu)
    have hsimplex_nonempty :
        ((fun u : Fin m → ℝ => ∑ i, r i * u i) '' standardSimplex m).Nonempty := by
      refine ⟨(∑ i, r i * (fun k : Fin m => if k = ⟨0, Nat.pos_of_ne_zero hm⟩ then (1 : ℝ) else 0) i), ?_⟩
      refine ⟨_, standardSimplex_basis_mem (n := m) ⟨0, Nat.pos_of_ne_zero hm⟩, rfl⟩
    have hsimplex_bdd :
        BddAbove ((fun u : Fin m → ℝ => ∑ i, r i * u i) '' standardSimplex m) := by
      refine ⟨sSup S, ?_⟩
      intro y hy
      rcases hy with ⟨u, hu, rfl⟩
      exact hlinear_le u hu
    have hS_nonempty : S.Nonempty := by
      refine ⟨r ⟨0, Nat.pos_of_ne_zero hm⟩, ?_⟩
      exact ⟨⟨0, Nat.pos_of_ne_zero hm⟩, by simp⟩
    apply le_antisymm
    · refine csSup_le hsimplex_nonempty ?_
      intro y hy
      rcases hy with ⟨u, hu, rfl⟩
      exact hlinear_le u hu
    · refine csSup_le hS_nonempty ?_
      intro y hy
      rcases hy with ⟨i, hi, rfl⟩
      have himg :
          r i ∈ ((fun u : Fin m → ℝ => ∑ i, r i * u i) '' standardSimplex m) := by
        refine ⟨_, standardSimplex_basis_mem (n := m) i, ?_⟩
        simp [mul_ite]
      exact le_csSup hsimplex_bdd himg

/-- Adding a constant commutes with `sSup` on a bounded nonempty set of reals. -/
lemma sSup_image_add_const {s : Set ℝ} (a : ℝ) (hs : BddAbove s) (hne : s.Nonempty) :
    sSup ((fun x => a + x) '' s) = a + sSup s := by
  classical
  rcases hne with ⟨x0, hx0⟩
  have hne' : s.Nonempty := ⟨x0, hx0⟩
  have himage_bdd : BddAbove ((fun x => a + x) '' s) := by
    refine ⟨a + sSup s, ?_⟩
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hx_le : x ≤ sSup s := le_csSup hs hx
    linarith
  have himage_nonempty : ((fun x => a + x) '' s).Nonempty := by
    exact ⟨a + x0, ⟨x0, hx0, rfl⟩⟩
  apply le_antisymm
  · refine (csSup_le_iff (s := ((fun x => a + x) '' s)) himage_bdd himage_nonempty).2 ?_
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hx_le : x ≤ sSup s := le_csSup hs hx
    linarith
  · refine (le_csSup_iff (s := ((fun x => a + x) '' s)) himage_bdd himage_nonempty).2 ?_
    intro b hb
    have hb' : ∀ x ∈ s, x ≤ b - a := by
      intro x hx
      have hb'' : a + x ≤ b := by
        have hb' : ∀ y ∈ ((fun x => a + x) '' s), y ≤ b := by
          simpa [upperBounds] using hb
        exact hb' (a + x) ⟨x, hx, rfl⟩
      linarith
    have hs_le : sSup s ≤ b - a := by
      exact (csSup_le_iff hs hne').2 hb'
    linarith

/-- Adding a constant commutes with `sInf` on a bounded-below nonempty set of reals. -/
lemma sInf_image_add_const {s : Set ℝ} (a : ℝ) (hs : BddBelow s) (hne : s.Nonempty) :
    sInf ((fun x => a + x) '' s) = a + sInf s := by
  classical
  rcases hne with ⟨x0, hx0⟩
  have hne' : s.Nonempty := ⟨x0, hx0⟩
  have himage_nonempty : ((fun x => a + x) '' s).Nonempty := by
    exact ⟨a + x0, ⟨x0, hx0, rfl⟩⟩
  have himage_bdd : BddBelow ((fun x => a + x) '' s) := by
    refine ⟨a + sInf s, ?_⟩
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hx_le : sInf s ≤ x := csInf_le hs hx
    linarith
  apply le_antisymm
  · have hbound : ∀ x ∈ s, sInf ((fun x => a + x) '' s) - a ≤ x := by
      intro x hx
      have hx' : sInf ((fun x => a + x) '' s) ≤ a + x := by
        exact csInf_le himage_bdd ⟨x, hx, rfl⟩
      linarith
    have hle : sInf ((fun x => a + x) '' s) - a ≤ sInf s := le_csInf hne' hbound
    linarith
  · refine le_csInf himage_nonempty ?_
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hx_le : sInf s ≤ x := csInf_le hs hx
    linarith

/-- Any linear functional value on the standard simplex is bounded below by the
infimum of its coefficients. -/
lemma sInf_coeff_le_linear_standardSimplex {m : ℕ} (r : Fin m → ℝ) :
    ∀ u ∈ standardSimplex m,
      sInf ((fun i : Fin m => r i) '' (Set.univ : Set (Fin m))) ≤ ∑ i, r i * u i := by
  classical
  intro u hu
  set S : Set ℝ := (fun i : Fin m => r i) '' (Set.univ : Set (Fin m)) with hS
  have hS_bdd : BddBelow S := by
    simp [hS, Set.image_univ]
  have hcoeff : ∀ i, sInf S ≤ r i := by
    intro i
    exact csInf_le hS_bdd ⟨i, by simp⟩
  have hle : ∑ i, sInf S * u i ≤ ∑ i, r i * u i := by
    refine Finset.sum_le_sum ?_
    intro i hi
    exact mul_le_mul_of_nonneg_right (hcoeff i) (hu.1 i)
  have hsum : ∑ i, sInf S * u i = sInf S := by
    calc
      ∑ i, sInf S * u i = sInf S * ∑ i, u i := by
        symm
        simpa using
          (Finset.mul_sum (s := (Finset.univ : Finset (Fin m))) (a := sInf S)
            (f := fun i => u i))
      _ = sInf S := by
        simp [hu.2]
  calc
    sInf S = ∑ i, sInf S * u i := hsum.symm
    _ ≤ ∑ i, r i * u i := hle

/-- The infimum of a linear functional over the standard simplex equals the infimum
of its coefficients. -/
lemma sInf_linear_standardSimplex_eq {m : ℕ} (r : Fin m → ℝ) :
    sInf ((fun u : Fin m → ℝ => ∑ i, r i * u i) '' standardSimplex m) =
      sInf ((fun i : Fin m => r i) '' (Set.univ : Set (Fin m))) := by
  classical
  by_cases hm : m = 0
  · subst hm
    simp [standardSimplex]
  · set S : Set ℝ := (fun u : Fin m → ℝ => ∑ i, r i * u i) '' standardSimplex m with hS
    set T : Set ℝ := (fun i : Fin m => r i) '' (Set.univ : Set (Fin m)) with hT
    have hT_nonempty : T.Nonempty := by
      classical
      refine ⟨r ⟨0, Nat.pos_of_ne_zero hm⟩, ?_⟩
      exact ⟨⟨0, Nat.pos_of_ne_zero hm⟩, by simp⟩
    have hlower : ∀ u ∈ standardSimplex m, sInf T ≤ ∑ i, r i * u i := by
      intro u hu
      simpa [hT] using (sInf_coeff_le_linear_standardSimplex (r := r) u hu)
    have hS_bdd : BddBelow S := by
      refine ⟨sInf T, ?_⟩
      intro y hy
      rcases hy with ⟨u, hu, rfl⟩
      exact hlower u hu
    have hS_nonempty : S.Nonempty := by
      classical
      refine ⟨(∑ i, r i * (fun k : Fin m => if k = ⟨0, Nat.pos_of_ne_zero hm⟩ then (1 : ℝ) else 0) i), ?_⟩
      refine ⟨_, standardSimplex_basis_mem (n := m) ⟨0, Nat.pos_of_ne_zero hm⟩, rfl⟩
    apply le_antisymm
    · refine le_csInf hT_nonempty ?_
      intro y hy
      rcases hy with ⟨i, hi, rfl⟩
      have himg :
          r i ∈ ((fun u : Fin m → ℝ => ∑ i, r i * u i) '' standardSimplex m) := by
        refine ⟨_, standardSimplex_basis_mem (n := m) i, ?_⟩
        simp [mul_ite]
      exact csInf_le hS_bdd himg
    · refine le_csInf hS_nonempty ?_
      intro y hy
      rcases hy with ⟨u, hu, rfl⟩
      exact hlower u hu

/-- Expanding the bilinear form `x ↦ ∑ j, (A x) j * u j` on the standard basis. -/
lemma sum_Ax_mul_eq_sum_basis {n m : ℕ} (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (u : Fin m → ℝ) (x : Fin n → ℝ) :
    ∑ j, (A x) j * u j =
      ∑ i, (∑ j, (A (fun k => if k = i then (1 : ℝ) else 0)) j * u j) * x i := by
  classical
  have hAx :
      A x =
        ∑ i, x i • A (fun k => if k = i then (1 : ℝ) else 0) := by
    simpa [eq_comm] using (LinearMap.pi_apply_eq_sum_univ (f := A) x)
  calc
    ∑ j, (A x) j * u j =
        ∑ j, (∑ i, x i * (A (fun k => if k = i then (1 : ℝ) else 0)) j) * u j := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          simp [hAx, Pi.smul_apply, smul_eq_mul]
    _ = ∑ j, ∑ i, x i * (A (fun k => if k = i then (1 : ℝ) else 0)) j * u j := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          calc
            (∑ i, x i * (A (fun k => if k = i then (1 : ℝ) else 0)) j) * u j
                = u j * ∑ i, x i * (A (fun k => if k = i then (1 : ℝ) else 0)) j := by
                    ring
            _ =
                ∑ i, u j * (x i * (A (fun k => if k = i then (1 : ℝ) else 0)) j) := by
                    simpa using
                      (Finset.mul_sum (s := (Finset.univ : Finset (Fin n))) (a := u j)
                        (f := fun i => x i * (A (fun k => if k = i then (1 : ℝ) else 0)) j))
            _ =
                ∑ i, x i * (A (fun k => if k = i then (1 : ℝ) else 0)) j * u j := by
                    refine Finset.sum_congr rfl ?_
                    intro i hi
                    ring
    _ = ∑ i, ∑ j, x i * (A (fun k => if k = i then (1 : ℝ) else 0)) j * u j := by
          simpa using (Finset.sum_comm)
    _ = ∑ i, x i * ∑ j, (A (fun k => if k = i then (1 : ℝ) else 0)) j * u j := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          calc
            ∑ j, x i * (A (fun k => if k = i then (1 : ℝ) else 0)) j * u j
                = ∑ j, x i * ((A (fun k => if k = i then (1 : ℝ) else 0)) j * u j) := by
                    refine Finset.sum_congr rfl ?_
                    intro j hj
                    ring
            _ =
                x i * ∑ j, (A (fun k => if k = i then (1 : ℝ) else 0)) j * u j := by
                    symm
                    simpa using
                      (Finset.mul_sum (s := (Finset.univ : Finset (Fin m))) (a := x i)
                        (f := fun j => (A (fun k => if k = i then (1 : ℝ) else 0)) j * u j))
    _ = ∑ i, (∑ j, (A (fun k => if k = i then (1 : ℝ) else 0)) j * u j) * x i := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          ring

/-- Rewriting the dual objective as an infimum over the standard simplex. -/
lemma matrixGameDualObjective_eq_sInf_over_standardSimplex (n m : ℕ)
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (c : Fin n → ℝ) (b : Fin m → ℝ)
    (u : Fin m → ℝ) (hne : (standardSimplex n).Nonempty) :
    matrixGameDualObjective n m A c b u =
      sInf
        ((fun x : Fin n → ℝ =>
              (∑ j, (A x) j * u j) + (∑ i, c i * x i) + (∑ j, b j * u j)) ''
          standardSimplex n) := by
  classical
  set r : Fin n → ℝ := fun i =>
      (∑ j, (A (fun k => if k = i then (1 : ℝ) else 0)) j * u j) + c i
  have hlin :
      (fun x : Fin n → ℝ => ∑ i, r i * x i) =
        fun x => (∑ j, (A x) j * u j) + (∑ i, c i * x i) := by
    funext x
    have hAx : ∑ j, (A x) j * u j =
        ∑ i, (∑ j, (A (fun k => if k = i then (1 : ℝ) else 0)) j * u j) * x i :=
      sum_Ax_mul_eq_sum_basis (A := A) (u := u) (x := x)
    calc
      ∑ i, r i * x i
          = ∑ i, ((∑ j, (A (fun k => if k = i then (1 : ℝ) else 0)) j * u j) + c i) * x i := by
              simp [r]
      _ =
          ∑ i, (∑ j, (A (fun k => if k = i then (1 : ℝ) else 0)) j * u j) * x i +
            ∑ i, c i * x i := by
              simp [add_mul, Finset.sum_add_distrib]
      _ = (∑ j, (A x) j * u j) + (∑ i, c i * x i) := by
              simp [hAx.symm]
  set S : Set ℝ := (fun x : Fin n → ℝ => ∑ i, r i * x i) '' standardSimplex n with hS
  have hS_bdd : BddBelow S := by
    set T : Set ℝ := (fun i : Fin n => r i) '' (Set.univ : Set (Fin n)) with hT
    refine ⟨sInf T, ?_⟩
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have h := sInf_coeff_le_linear_standardSimplex (r := r) x hx
    simpa [hT] using h
  have hconst :
      sInf ((fun x => (∑ j, b j * u j) + ∑ i, r i * x i) '' standardSimplex n) =
        (∑ j, b j * u j) + sInf S := by
    have hS_nonempty : S.Nonempty := by
      rcases hne with ⟨x, hx⟩
      exact ⟨_, ⟨x, hx, rfl⟩⟩
    simpa [S, Set.image_image, Function.comp] using
      (sInf_image_add_const (a := ∑ j, b j * u j) (s := S) hS_bdd hS_nonempty)
  have hInf : sInf (Set.range fun i : Fin n => r i) = sInf S := by
    simpa [S, Set.image_univ] using (sInf_linear_standardSimplex_eq (r := r)).symm
  calc
    matrixGameDualObjective n m A c b u =
        (∑ j, b j * u j) +
          sInf ((fun i : Fin n => r i) '' (Set.univ : Set (Fin n))) := by
          simp [matrixGameDualObjective, r]
    _ = (∑ j, b j * u j) + sInf S := by
          simp [Set.image_univ, hInf]
    _ =
        sInf
          ((fun x => (∑ j, b j * u j) + ∑ i, r i * x i) '' standardSimplex n) := by
          symm
          exact hconst
    _ =
        sInf
          ((fun x : Fin n → ℝ =>
              (∑ j, (A x) j * u j) + (∑ i, c i * x i) + (∑ j, b j * u j)) ''
            standardSimplex n) := by
          refine congrArg sInf ?_
          refine Set.image_congr ?_
          intro x hx
          have hlinx := congrArg (fun f => f x) hlin
          simp [hlinx, add_left_comm, add_comm]

/-- Pointwise weak duality for a fixed dual vector in the simplex. -/
lemma matrixGameDualObjective_le_saddlePointValue (n m : ℕ)
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (c : Fin n → ℝ) (b : Fin m → ℝ)
    (u : Fin m → ℝ) (hu : u ∈ standardSimplex m) (hne : (standardSimplex n).Nonempty) :
    matrixGameDualObjective n m A c b u ≤ matrixGameSaddlePointValue n m A c b := by
  classical
  have hne_img :
      ((fun x =>
          sSup
            ((fun u' =>
                (∑ i, (A x) i * u' i) + (∑ i, c i * x i) + (∑ i, b i * u' i)) ''
              standardSimplex m)) '' standardSimplex n).Nonempty := by
    rcases hne with ⟨x, hx⟩
    exact ⟨_, ⟨x, hx, rfl⟩⟩
  refine le_csInf hne_img ?_
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  set r : Fin n → ℝ := fun i =>
      (∑ j, (A (fun k => if k = i then (1 : ℝ) else 0)) j * u j) + c i
  have hsum :
      ∑ i, (∑ j, (A (fun k => if k = i then (1 : ℝ) else 0)) j * u j) * x i =
        ∑ j, (A x) j * u j := by
    symm
    exact sum_Ax_mul_eq_sum_basis (A := A) (u := u) (x := x)
  have hAx :
      ∑ i, r i * x i = (∑ j, (A x) j * u j) + (∑ i, c i * x i) := by
    calc
      ∑ i, r i * x i
          = ∑ i, ((∑ j, (A (fun k => if k = i then (1 : ℝ) else 0)) j * u j) + c i) * x i := by
              simp [r]
      _ =
          ∑ i, (∑ j, (A (fun k => if k = i then (1 : ℝ) else 0)) j * u j) * x i +
            ∑ i, c i * x i := by
              simp [add_mul, Finset.sum_add_distrib]
      _ = (∑ j, (A x) j * u j) + ∑ i, c i * x i := by
              simp [hsum, add_comm]
  have hcoeff :
      sInf ((fun i : Fin n => r i) '' (Set.univ : Set (Fin n))) ≤
        (∑ j, (A x) j * u j) + (∑ i, c i * x i) := by
    have h := sInf_coeff_le_linear_standardSimplex (r := r) x hx
    simpa [hAx] using h
  have hle_payoff :
      matrixGameDualObjective n m A c b u ≤
        (∑ j, (A x) j * u j) + (∑ i, c i * x i) + (∑ j, b j * u j) := by
    calc
      matrixGameDualObjective n m A c b u
          = (∑ j, b j * u j) +
              sInf ((fun i : Fin n => r i) '' (Set.univ : Set (Fin n))) := by
                simp [matrixGameDualObjective, r]
      _ ≤ (∑ j, b j * u j) + ((∑ j, (A x) j * u j) + (∑ i, c i * x i)) := by
            have h := add_le_add_left hcoeff (∑ j, b j * u j)
            simpa [add_comm, add_left_comm, add_assoc] using h
      _ = (∑ j, (A x) j * u j) + (∑ i, c i * x i) + (∑ j, b j * u j) := by
            ring
  set r' : Fin m → ℝ := fun j => (A x) j + b j
  have hbdd :
      BddAbove
        ((fun u' =>
            (∑ j, (A x) j * u' j) + (∑ i, c i * x i) + (∑ j, b j * u' j)) ''
          standardSimplex m) := by
    refine ⟨(∑ i, c i * x i) + sSup ((fun j : Fin m => r' j) '' (Set.univ : Set (Fin m))), ?_⟩
    intro y hy
    rcases hy with ⟨u', hu', rfl⟩
    have hlin :
        (∑ j, (A x) j * u' j) + (∑ j, b j * u' j) = ∑ j, r' j * u' j := by
      calc
        (∑ j, (A x) j * u' j) + (∑ j, b j * u' j)
            = ∑ j, (A x) j * u' j + ∑ j, b j * u' j := rfl
        _ = ∑ j, ((A x) j * u' j + b j * u' j) := by
              symm
              simpa using
                (Finset.sum_add_distrib (s := (Finset.univ : Finset (Fin m)))
                  (f := fun j => (A x) j * u' j) (g := fun j => b j * u' j))
        _ = ∑ j, ((A x) j + b j) * u' j := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              simp [add_mul]
        _ = ∑ j, r' j * u' j := by simp [r']
    have hle_lin :
        ∑ j, r' j * u' j ≤ sSup ((fun j : Fin m => r' j) '' (Set.univ : Set (Fin m))) := by
      simpa using (linear_standardSimplex_le_sSup_coeff (r := r') u' hu')
    have hrewrite :
        (∑ j, (A x) j * u' j) + (∑ i, c i * x i) + (∑ j, b j * u' j) =
          (∑ i, c i * x i) + ∑ j, r' j * u' j := by
      calc
        (∑ j, (A x) j * u' j) + (∑ i, c i * x i) + (∑ j, b j * u' j)
            = (∑ i, c i * x i) + ((∑ j, (A x) j * u' j) + (∑ j, b j * u' j)) := by
                ring
        _ = (∑ i, c i * x i) + ∑ j, r' j * u' j := by simp [hlin]
    calc
      (∑ j, (A x) j * u' j) + (∑ i, c i * x i) + (∑ j, b j * u' j)
          = (∑ i, c i * x i) + ∑ j, r' j * u' j := hrewrite
      _ ≤ (∑ i, c i * x i) + sSup ((fun j : Fin m => r' j) '' (Set.univ : Set (Fin m))) :=
            by
              have h := add_le_add_left hle_lin (∑ i, c i * x i)
              simpa [add_comm, add_left_comm, add_assoc] using h
  have hle_sup :
      (∑ j, (A x) j * u j) + (∑ i, c i * x i) + (∑ j, b j * u j) ≤
        sSup
          ((fun u' =>
              (∑ j, (A x) j * u' j) + (∑ i, c i * x i) + (∑ j, b j * u' j)) ''
            standardSimplex m) := by
    exact le_csSup hbdd ⟨u, hu, rfl⟩
  exact hle_payoff.trans hle_sup

/-- Weak duality: the dual value is bounded above by the saddle-point value. -/
lemma matrixGameDual_le_saddlePointValue (n m : ℕ)
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (c : Fin n → ℝ) (b : Fin m → ℝ)
    (hm : 0 < m) (hne : (standardSimplex n).Nonempty) :
    sSup ((matrixGameDualObjective n m A c b) '' standardSimplex m) ≤
      matrixGameSaddlePointValue n m A c b := by
  classical
  have hne_m : (standardSimplex m).Nonempty := standardSimplex_nonempty_of_pos hm
  have hne_img :
      ((matrixGameDualObjective n m A c b) '' standardSimplex m).Nonempty := by
    rcases hne_m with ⟨u, hu⟩
    exact ⟨_, ⟨u, hu, rfl⟩⟩
  refine csSup_le hne_img ?_
  intro y hy
  rcases hy with ⟨u, hu, rfl⟩
  exact
    matrixGameDualObjective_le_saddlePointValue (n := n) (m := m) (A := A) (c := c) (b := b)
      (u := u) hu hne

/-- Definition 1.4.1.2.
The saddle-point value (4.9) equals the primal minimization in (4.10) and upper-bounds the
dual maximization in (4.10_dual) over the standard simplices `Δ_n` and `Δ_m`. -/
theorem matrixGameSaddlePointValue_eq_primal_dual (n m : ℕ)
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (c : Fin n → ℝ) (b : Fin m → ℝ) (hn : 0 < n)
    (hm : 0 < m) :
    matrixGameSaddlePointValue n m A c b =
        sInf ((matrixGamePrimalObjective n m A c b) '' standardSimplex n) ∧
      sSup ((matrixGameDualObjective n m A c b) '' standardSimplex m) ≤
        matrixGameSaddlePointValue n m A c b := by
  classical
  constructor
  · have hprimal :
        (fun x =>
            sSup
              ((fun u =>
                    (∑ i, (A x) i * u i) + (∑ i, c i * x i) + (∑ i, b i * u i)) ''
                standardSimplex m)) =
          matrixGamePrimalObjective n m A c b := by
        funext x
        set r : Fin m → ℝ := fun i => (A x) i + b i
        have hfun :
            (fun u : Fin m → ℝ =>
                (∑ i, (A x) i * u i) + (∑ i, c i * x i) + (∑ i, b i * u i)) =
              fun u => (∑ i, c i * x i) + ∑ i, r i * u i := by
          funext u
          have hsum :
              (∑ i, (A x) i * u i) + (∑ i, b i * u i) = ∑ i, r i * u i := by
            calc
              (∑ i, (A x) i * u i) + (∑ i, b i * u i)
                  = ∑ i, (A x) i * u i + ∑ i, b i * u i := rfl
              _ = ∑ i, ((A x) i * u i + b i * u i) := by
                symm
                simpa using
                  (Finset.sum_add_distrib (s := (Finset.univ : Finset (Fin m)))
                    (f := fun i => (A x) i * u i) (g := fun i => b i * u i))
              _ = ∑ i, ((A x) i + b i) * u i := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                simp [add_mul]
              _ = ∑ i, r i * u i := by simp [r]
          calc
            (∑ i, (A x) i * u i) + (∑ i, c i * x i) + (∑ i, b i * u i)
                = (∑ i, c i * x i) + ((∑ i, (A x) i * u i) + (∑ i, b i * u i)) := by ring
            _ = (∑ i, c i * x i) + ∑ i, r i * u i := by simp [hsum]
        have hconst :
            sSup ((fun u => (∑ i, c i * x i) + ∑ i, r i * u i) '' standardSimplex m) =
              (∑ i, c i * x i) + sSup ((fun u => ∑ i, r i * u i) '' standardSimplex m) := by
          set s : Set ℝ := ((fun u : Fin m → ℝ => ∑ i, r i * u i) '' standardSimplex m)
          have hs : BddAbove s := by
            refine ⟨sSup ((fun i : Fin m => r i) '' (Set.univ : Set (Fin m))), ?_⟩
            intro y hy
            rcases hy with ⟨u, hu, rfl⟩
            simpa using (linear_standardSimplex_le_sSup_coeff (r := r) u hu)
          have hS_nonempty : s.Nonempty := by
            rcases standardSimplex_nonempty_of_pos (n := m) hm with ⟨u, hu⟩
            exact ⟨_, ⟨u, hu, rfl⟩⟩
          simpa [s, Set.image_image, Function.comp] using
            (sSup_image_add_const (a := ∑ i, c i * x i) (s := s) hs hS_nonempty)
        have hsup :
            sSup ((fun u : Fin m → ℝ => ∑ i, r i * u i) '' standardSimplex m) =
              sSup ((fun i : Fin m => r i) '' (Set.univ : Set (Fin m))) := by
          simpa using (sSup_linear_standardSimplex_eq (r := r))
        calc
          sSup
              ((fun u =>
                    (∑ i, (A x) i * u i) + (∑ i, c i * x i) + (∑ i, b i * u i)) ''
                standardSimplex m)
              =
              sSup ((fun u => (∑ i, c i * x i) + ∑ i, r i * u i) '' standardSimplex m) := by
                simp [hfun]
          _ =
              (∑ i, c i * x i) + sSup ((fun u : Fin m → ℝ => ∑ i, r i * u i) '' standardSimplex m) :=
                hconst
          _ =
              (∑ i, c i * x i) + sSup ((fun i : Fin m => r i) '' (Set.univ : Set (Fin m))) :=
                by simp [hsup]
          _ = matrixGamePrimalObjective n m A c b x := by
                simp [matrixGamePrimalObjective, r]
    simp [matrixGameSaddlePointValue, hprimal]
  ·
    have hne : (standardSimplex n).Nonempty := standardSimplex_nonempty_of_pos hn
    simpa using
      (matrixGameDual_le_saddlePointValue (n := n) (m := m) (A := A) (c := c) (b := b) hm hne)

/-- A coordinate of a point in the standard simplex lies in `[0, 1]`. -/
lemma standardSimplex_coord_mem_Icc {n : ℕ} {x : Fin n → ℝ} (hx : x ∈ standardSimplex n) :
    ∀ i, x i ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  intro i
  refine ⟨hx.1 i, ?_⟩
  have hle' : x i ≤ ∑ j ∈ (Finset.univ : Finset (Fin n)), x j := by
    refine Finset.single_le_sum ?_ (by simp)
    intro j hj
    exact hx.1 j
  have hle : x i ≤ ∑ j, x j := by
    simpa using hle'
  calc
    x i ≤ ∑ j, x j := hle
    _ = (1 : ℝ) := hx.2

/-- The squared `Pi`/sup norm on `Fin n → ℝ` is bounded by the sum of squared coordinates. -/
lemma norm_sq_le_sum_sq_pi (n : ℕ) (z : Fin n → ℝ) :
    ‖z‖ ^ (2 : ℕ) ≤ ∑ i, (z i) ^ (2 : ℕ) := by
  classical
  by_cases hn : n = 0
  · subst hn
    simp [Pi.norm_def]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have : Nonempty (Fin n) := ⟨⟨0, hnpos⟩⟩
    have huniv : (Finset.univ : Finset (Fin n)).Nonempty := Finset.univ_nonempty
    set f : Fin n → ℝ≥0 := fun i => ‖z i‖₊
    rcases Finset.exists_mem_eq_sup (s := Finset.univ) huniv f with ⟨i0, hi0, hsup⟩
    have hnorm : ‖z‖ = ‖z i0‖ := by
      simp [Pi.norm_def, f, hsup]
    have hle' : ‖z i0‖ ^ (2 : ℕ) ≤ ∑ i, ‖z i‖ ^ (2 : ℕ) := by
      have hle'' :
          ‖z i0‖ ^ (2 : ℕ) ≤
            ∑ i ∈ (Finset.univ : Finset (Fin n)), ‖z i‖ ^ (2 : ℕ) := by
        refine
          Finset.single_le_sum (s := (Finset.univ : Finset (Fin n)))
            (f := fun i => ‖z i‖ ^ (2 : ℕ)) ?_ hi0
        intro i hi
        exact pow_two_nonneg ‖z i‖
      simpa using hle''
    calc
      ‖z‖ ^ (2 : ℕ) = ‖z i0‖ ^ (2 : ℕ) := by simp [hnorm]
      _ ≤ ∑ i, ‖z i‖ ^ (2 : ℕ) := hle'
      _ = ∑ i, (z i) ^ (2 : ℕ) := by
        simp [Real.norm_eq_abs]

/-- Derivative formula for `x ↦ x * log x - (1/2) * x^2` away from `0`. -/
lemma deriv_mul_log_sub_half_sq {x : ℝ} (hx : x ≠ 0) :
    deriv (fun t : ℝ => t * Real.log t - (1 / 2 : ℝ) * t ^ 2) x = Real.log x + 1 - x := by
  have hdiff1 : DifferentiableAt ℝ (fun t : ℝ => t * Real.log t) x :=
    (Real.hasDerivAt_mul_log hx).differentiableAt
  have hdiff2 : DifferentiableAt ℝ (fun t : ℝ => (1 / 2 : ℝ) * t ^ 2) x := by
    simp
  have hsub :=
    deriv_sub (f := fun t : ℝ => t * Real.log t) (g := fun t : ℝ => (1 / 2 : ℝ) * t ^ 2)
      (x := x) (hf := hdiff1) (hg := hdiff2)
  have hquad : deriv (fun t : ℝ => (1 / 2 : ℝ) * t ^ 2) x = x := by
    simp [pow_two]
    ring
  simpa [Real.deriv_mul_log hx, hquad] using hsub

/-- Second derivative formula for `x ↦ x * log x - (1/2) * x^2` away from `0`. -/
lemma deriv2_mul_log_sub_half_sq {x : ℝ} (hx : x ≠ 0) :
    deriv^[2] (fun t : ℝ => t * Real.log t - (1 / 2 : ℝ) * t ^ 2) x = x⁻¹ - 1 := by
  simp only [Function.iterate_succ, Function.iterate_zero, Function.id_comp, Function.comp_apply]
  suffices
      ∀ᶠ y in nhds x,
        deriv (fun t : ℝ => t * Real.log t - (1 / 2 : ℝ) * t ^ 2) y = Real.log y + 1 - y by
    refine (Filter.EventuallyEq.deriv_eq this).trans ?_
    have hdiff : DifferentiableAt ℝ (fun y : ℝ => Real.log y + 1) x :=
      (Real.differentiableAt_log hx).add (differentiableAt_const _)
    have h :=
      deriv_sub (f := fun y : ℝ => Real.log y + 1) (g := fun y : ℝ => y) (x := x)
        (hf := hdiff) (hg := differentiableAt_id)
    simpa [sub_eq_add_neg, deriv_add_const, Real.deriv_log] using h
  filter_upwards [eventually_ne_nhds hx] with y hy using deriv_mul_log_sub_half_sq (x := y) hy

/-- On `[0,1]`, `x ↦ x * log x` is `1`-strongly convex. -/
lemma mul_log_strongConvexOn_Icc :
    StrongConvexOn (Set.Icc (0 : ℝ) 1) 1 (fun t : ℝ => t * Real.log t) := by
  -- use `StrongConvexOn`'s characterization on `ℝ` as convexity of `f(x) - (1/2) * ‖x‖^2`
  rw [strongConvexOn_iff_convex]
  -- rewrite `‖x‖^2` as `x^2` on `ℝ`
  have hconv :
      ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (fun t : ℝ => t * Real.log t - (1 / 2 : ℝ) * t ^ 2) := by
    refine
      convexOn_of_deriv2_nonneg (D := Set.Icc (0 : ℝ) 1) (f := fun t : ℝ =>
        t * Real.log t - (1 / 2 : ℝ) * t ^ 2) (hD := convex_Icc _ _) ?_ ?_ ?_ ?_
    · -- continuity on `[0,1]`
      have h1 : Continuous fun t : ℝ => t * Real.log t := Real.continuous_mul_log
      have h2 : Continuous fun t : ℝ => (1 / 2 : ℝ) * t ^ 2 := by
        simpa using (continuous_const.mul ((continuous_id).pow 2))
      exact (h1.sub h2).continuousOn
    · -- differentiability on the interior `(0,1)`
      have hsubset : Set.Ioo (0 : ℝ) 1 ⊆ ({0} : Set ℝ)ᶜ := by
        intro t ht
        simp [Set.mem_compl_iff, Set.mem_singleton_iff, ne_of_gt ht.1]
      have hmulLog :
          DifferentiableOn ℝ (fun t : ℝ => t * Real.log t) (Set.Ioo (0 : ℝ) 1) :=
        Real.differentiableOn_mul_log.mono hsubset
      have hquad' : Differentiable ℝ (fun t : ℝ => (1 / 2 : ℝ) * t ^ 2) := by
        simp
      have hquad :
          DifferentiableOn ℝ (fun t : ℝ => (1 / 2 : ℝ) * t ^ 2) (Set.Ioo (0 : ℝ) 1) :=
        hquad'.differentiableOn
      simpa [interior_Icc] using hmulLog.sub hquad
    · -- differentiability of the derivative on the interior `(0,1)`
      have hsubset : Set.Ioo (0 : ℝ) 1 ⊆ ({0} : Set ℝ)ᶜ := by
        intro t ht
        simp [Set.mem_compl_iff, Set.mem_singleton_iff, ne_of_gt ht.1]
      have hderivEq :
          ∀ t ∈ Set.Ioo (0 : ℝ) 1,
            deriv (fun u : ℝ => u * Real.log u - (1 / 2 : ℝ) * u ^ 2) t = Real.log t + 1 - t := by
        intro t ht
        exact deriv_mul_log_sub_half_sq (x := t) (ne_of_gt ht.1)
      have hExp :
          DifferentiableOn ℝ (fun t : ℝ => Real.log t + 1 - t) (Set.Ioo (0 : ℝ) 1) := by
        have hlog : DifferentiableOn ℝ Real.log (Set.Ioo (0 : ℝ) 1) :=
          Real.differentiableOn_log.mono hsubset
        have hconst : DifferentiableOn ℝ (fun _ : ℝ => (1 : ℝ)) (Set.Ioo (0 : ℝ) 1) :=
          differentiableOn_const (c := (1 : ℝ))
        have : DifferentiableOn ℝ (fun t : ℝ => (Real.log t + 1) - t) (Set.Ioo (0 : ℝ) 1) :=
          (hlog.add hconst).sub differentiableOn_id
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
      have hderiv :
          DifferentiableOn ℝ
            (deriv (fun u : ℝ => u * Real.log u - (1 / 2 : ℝ) * u ^ 2)) (Set.Ioo (0 : ℝ) 1) :=
        hExp.congr (by intro t ht; exact hderivEq t ht)
      simpa [interior_Icc] using hderiv
    · -- second derivative nonnegativity on the interior `(0,1)`
      intro t ht
      have ht' : t ∈ Set.Ioo (0 : ℝ) 1 := by simpa [interior_Icc] using ht
      have ht0 : t ≠ 0 := ne_of_gt ht'.1
      have ht1 : t ≤ 1 := le_of_lt ht'.2
      have htpos : 0 < t := ht'.1
      have hderiv2 := deriv2_mul_log_sub_half_sq (x := t) ht0
      -- `0 < t ≤ 1` implies `1 ≤ t⁻¹`, hence `0 ≤ t⁻¹ - 1`
      have hinv : (1 : ℝ) ≤ t⁻¹ := (one_le_inv₀ htpos).2 ht1
      rw [hderiv2]
      exact sub_nonneg.mpr hinv
  -- convert back from `t^2` to `‖t‖^2`
  simpa [Real.norm_eq_abs, pow_two, abs_mul_self, sub_eq_add_neg, add_assoc, add_left_comm,
    add_comm, mul_assoc, mul_left_comm, mul_comm] using hconv

/-- The entropy sum `x ↦ ∑ i, x i * log (x i)` is `1`-strongly convex on the standard simplex. -/
lemma entropy_sum_strongConvexOn_standardSimplex (n : ℕ) :
    StrongConvexOn (standardSimplex n) 1 (fun x : Fin n → ℝ => ∑ i, x i * Real.log (x i)) := by
  classical
  unfold StrongConvexOn
  refine ⟨?_, ?_⟩
  · simpa [standardSimplex_eq_stdSimplex] using (convex_stdSimplex ℝ (Fin n))
  · intro x hx y hy a b ha hb hab
    have hxIcc := standardSimplex_coord_mem_Icc (x := x) hx
    have hyIcc := standardSimplex_coord_mem_Icc (x := y) hy
    have hcoord :
        ∀ i : Fin n,
          ((a • x + b • y) i) * Real.log ((a • x + b • y) i) ≤
            a • (x i * Real.log (x i)) + b • (y i * Real.log (y i)) -
              a * b * ((1 : ℝ) / 2 * ‖x i - y i‖ ^ 2) := by
      intro i
      simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using
        (mul_log_strongConvexOn_Icc).2 (hxIcc i) (hyIcc i) ha hb hab
    have hsum0 :
        (∑ i, ((a • x + b • y) i) * Real.log ((a • x + b • y) i)) ≤
          ∑ i,
            (a • (x i * Real.log (x i)) + b • (y i * Real.log (y i)) -
              a * b * ((1 : ℝ) / 2 * ‖x i - y i‖ ^ 2)) := by
      -- work directly with `Finset.univ.sum` to avoid simp-normalization of sums
      change
          (Finset.univ.sum fun i : Fin n =>
              ((a • x + b • y) i) * Real.log ((a • x + b • y) i)) ≤
            Finset.univ.sum fun i : Fin n =>
              (a • (x i * Real.log (x i)) + b • (y i * Real.log (y i)) -
                a * b * ((1 : ℝ) / 2 * ‖x i - y i‖ ^ (2 : ℕ)))
      refine Finset.sum_le_sum ?_
      intro i hi
      exact hcoord i
    have hsum1 :
        (∑ i,
            (a • (x i * Real.log (x i)) + b • (y i * Real.log (y i)) -
              a * b * ((1 : ℝ) / 2 * ‖x i - y i‖ ^ (2 : ℕ)))) =
          a • (∑ i, x i * Real.log (x i)) + b • (∑ i, y i * Real.log (y i)) -
            a * b * (((1 : ℝ) / 2) * ∑ i, ‖x i - y i‖ ^ (2 : ℕ)) := by
      simp [smul_eq_mul, sub_eq_add_neg, Finset.sum_add_distrib, Finset.mul_sum, add_comm, mul_assoc,
        mul_comm]
    have hnormSq : ‖x - y‖ ^ (2 : ℕ) ≤ ∑ i, ‖x i - y i‖ ^ (2 : ℕ) := by
      have h :=
        norm_sq_le_sum_sq_pi (n := n) (z := x - y)
      simpa [Pi.sub_apply, Real.norm_eq_abs, pow_two, abs_mul_self] using h
    have hab0 : 0 ≤ a * b := mul_nonneg ha hb
    have hhalf :
        ((1 : ℝ) / 2) * (‖x - y‖ ^ (2 : ℕ)) ≤ ((1 : ℝ) / 2) * ∑ i, ‖x i - y i‖ ^ (2 : ℕ) := by
      exact mul_le_mul_of_nonneg_left hnormSq (by norm_num)
    have hpen :
        a * b * (((1 : ℝ) / 2) * (‖x - y‖ ^ (2 : ℕ))) ≤
          a * b * (((1 : ℝ) / 2) * ∑ i, ‖x i - y i‖ ^ (2 : ℕ)) := by
      exact mul_le_mul_of_nonneg_left hhalf hab0
    have hrelax :
        a • (∑ i, x i * Real.log (x i)) + b • (∑ i, y i * Real.log (y i)) -
            a * b * (((1 : ℝ) / 2) * ∑ i, ‖x i - y i‖ ^ (2 : ℕ)) ≤
          a • (∑ i, x i * Real.log (x i)) + b • (∑ i, y i * Real.log (y i)) -
            a * b * ((1 : ℝ) / 2 * ‖x - y‖ ^ (2 : ℕ)) := by
      -- `‖x - y‖^2 ≤ ∑ ‖x_i - y_i‖^2` gives the relaxation under subtraction
      have hpen' :
          a * b * (((1 : ℝ) / 2) * (‖x - y‖ ^ (2 : ℕ))) ≤
            a * b * (((1 : ℝ) / 2) * ∑ i, ‖x i - y i‖ ^ (2 : ℕ)) := hpen
      exact sub_le_sub_left hpen' _
    have hsum0'' :
        (∑ i, ((a • x + b • y) i) * Real.log ((a • x + b • y) i)) ≤
          a • (∑ i, x i * Real.log (x i)) + b • (∑ i, y i * Real.log (y i)) -
            a * b * (((1 : ℝ) / 2) * ∑ i, ‖x i - y i‖ ^ (2 : ℕ)) := by
      calc
        (∑ i, ((a • x + b • y) i) * Real.log ((a • x + b • y) i)) ≤
            (∑ i,
                (a • (x i * Real.log (x i)) + b • (y i * Real.log (y i)) -
                  a * b * ((1 : ℝ) / 2 * ‖x i - y i‖ ^ (2 : ℕ)))) := hsum0
        _ =
            a • (∑ i, x i * Real.log (x i)) + b • (∑ i, y i * Real.log (y i)) -
              a * b * (((1 : ℝ) / 2) * ∑ i, ‖x i - y i‖ ^ (2 : ℕ)) := hsum1
    exact le_trans hsum0'' hrelax

/-- Adding a constant to a strongly convex function preserves strong convexity. -/
lemma StrongConvexOn.const_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set E} {m : ℝ} {f : E → ℝ} (c : ℝ) (hf : StrongConvexOn s m f) :
    StrongConvexOn s m (fun x => c + f x) := by
  refine ⟨hf.1, ?_⟩
  intro x hx y hy a b ha hb hab
  set P : ℝ := a * b * (fun r ↦ m / (2 : ℝ) * r ^ 2) ‖x - y‖
  have hP : f (a • x + b • y) ≤ a • f x + b • f y - P := by
    simpa [P] using hf.2 hx hy ha hb hab
  have hc : c = a * c + b * c := by
    calc
      c = (1 : ℝ) * c := by ring
      _ = (a + b) * c := by simp [hab]
      _ = a * c + b * c := by ring
  have hEq :
      c + (a • f x + b • f y - P) = a • (c + f x) + b • (c + f y) - P := by
    -- rewrite `c` as `a*c + b*c` and expand the scalar multiplications
    simp only [smul_eq_mul]
    calc
      c + (a * f x + b * f y - P) = (a * c + b * c) + (a * f x + b * f y - P) := by
        nth_rewrite 1 [hc]
        rfl
      _ = a * (c + f x) + b * (c + f y) - P := by ring
  calc
    c + f (a • x + b • y) ≤ c + (a • f x + b • f y - P) := by
      -- `add_le_add_right` gives `f(..)+c ≤ ..+c`; commute the terms using `ac_rfl`
      have hPc : f (a • x + b • y) + c ≤ (a • f x + b • f y - P) + c :=
        add_le_add_left hP c
      convert hPc using 1 <;> ac_rfl
    _ = a • (c + f x) + b • (c + f y) - P := hEq

/-- The entropy prox-function has prox-diameter bounded by `log n` on the standard simplex. -/
lemma entropy_proxDiameterBound_standardSimplex (n : ℕ) :
    IsProxDiameterBound (standardSimplex n)
      (fun x : Fin n → ℝ => Real.log (n : ℝ) + ∑ i, x i * Real.log (x i)) (Real.log (n : ℝ)) := by
  classical
  intro x hx
  have hxIcc := standardSimplex_coord_mem_Icc (x := x) hx
  have hsum_nonpos : (∑ i, x i * Real.log (x i)) ≤ 0 := by
    have h' :
        (Finset.univ.sum fun i : Fin n => x i * Real.log (x i)) ≤
          (Finset.univ.sum fun _ : Fin n => (0 : ℝ)) := by
      refine Finset.sum_le_sum ?_
      intro i hi
      have hxi := hxIcc i
      exact Real.mul_log_nonpos hxi.1 hxi.2
    simpa using h'
  linarith

/-- Lemma 1.4.1.1.
In the setting of Definition 1.4.1.2, with ℓ1 norms
`‖x‖₁ = ∑ i |x i|` and `‖u‖₁ = ∑ j |u j|`, and entropy prox-functions on `Δ_n` and `Δ_m`,
`d1(x) = ln n + ∑ i x^{(i)} ln x^{(i)}` and `d2(u) = ln m + ∑ j u^{(j)} ln u^{(j)}`,
the strong convexity parameters satisfy `σ1 = σ2 = 1` and the prox-diameters are
`D1 = ln n` and `D2 = ln m`. -/
theorem matrixGame_entropy_prox_parameters (n m : ℕ) :
    let d1 : (Fin n → ℝ) → ℝ :=
      fun x => Real.log (n : ℝ) + ∑ i, x i * Real.log (x i)
    let d2 : (Fin m → ℝ) → ℝ :=
      fun u => Real.log (m : ℝ) + ∑ j, u j * Real.log (u j)
    StrongConvexOn (standardSimplex n) 1 d1 ∧
      StrongConvexOn (standardSimplex m) 1 d2 ∧
      IsProxDiameterBound (standardSimplex n) d1 (Real.log (n : ℝ)) ∧
      IsProxDiameterBound (standardSimplex m) d2 (Real.log (m : ℝ)) := by
  classical
  dsimp
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- strong convexity of `d1`
    simpa using
      (StrongConvexOn.const_add (c := Real.log (n : ℝ))
        (entropy_sum_strongConvexOn_standardSimplex (n := n)))
  · -- strong convexity of `d2`
    simpa using
      (StrongConvexOn.const_add (c := Real.log (m : ℝ))
        (entropy_sum_strongConvexOn_standardSimplex (n := m)))
  · -- prox-diameter bound for `d1`
    simpa using entropy_proxDiameterBound_standardSimplex (n := n)
  · -- prox-diameter bound for `d2`
    simpa using entropy_proxDiameterBound_standardSimplex (n := m)

/-- The softmax normalizer `∑ exp(s j / μ)` is positive when `m > 0`. -/
lemma entropySimplex_softmax_den_pos (m : ℕ) (μ : ℝ) (s : Fin m → ℝ) (hm : 0 < m) :
    0 < ∑ j : Fin m, Real.exp (s j / μ) := by
  classical
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hne : (Finset.univ : Finset (Fin m)).Nonempty := by
    simp
  have hpos : 0 < (Finset.univ.sum fun j : Fin m => Real.exp (s j / μ)) := by
    refine
      Finset.sum_pos (s := (Finset.univ : Finset (Fin m))) (f := fun j => Real.exp (s j / μ))
        (by
          intro j hj
          simpa using (Real.exp_pos (s j / μ)))
        hne
  simpa using hpos

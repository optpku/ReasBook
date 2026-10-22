/-
Authors: Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Papers/SmoothMinimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib
import SmoothMinimization_Nesterov_2004.section04_part6

open scoped NNReal

namespace Section04Part7

/-- Proposition 1.4.1.2.
Under the entropy-distance setup of Lemma 1.4.1.1, the operator norm satisfies
`‖A‖_{1,2} = max_{‖x‖_1=1} ‖A x‖_{2,*} = max_{i,j} |A^{(i,j)}|` (eq:opnorm_entropy).
Consequently, since `M = 0` for the linear term `fhat(x) = ⟪c,x⟫_1`, the estimate (4.3) of
Theorem 1.4.1 becomes
`0 ≤ f(ĥx) - φ(ĥu) ≤ (4 * sqrt(ln n ln m)/(N+1)) * max_{i,j} |A^{(i,j)}|` (4.12). -/
theorem matrixGame_entropy_opNorm_bound (n m : ℕ)
    (A :
      (PiLp (1 : ENNReal) (fun _ : Fin n => ℝ)) →L[ℝ]
        ((PiLp (1 : ENNReal) (fun _ : Fin m => ℝ)) →L[ℝ] ℝ))
    (f : (PiLp (1 : ENNReal) (fun _ : Fin n => ℝ)) → ℝ)
    (φ : (PiLp (1 : ENNReal) (fun _ : Fin m => ℝ)) → ℝ)
    (xhat : PiLp (1 : ENNReal) (fun _ : Fin n => ℝ))
    (uhat : PiLp (1 : ENNReal) (fun _ : Fin m => ℝ)) (N : ℕ) :
    let A' :
        (PiLp (1 : ENNReal) (fun _ : Fin n => ℝ)) →ₗ[ℝ]
          Module.Dual ℝ (PiLp (1 : ENNReal) (fun _ : Fin m => ℝ)) :=
      { toFun := fun x => (A x).toLinearMap
        map_add' := by
          intro x y
          ext u
          simp
        map_smul' := by
          intro r x
          ext u
          simp }
    let AEntry : Fin n → Fin m → ℝ :=
      fun i j =>
        A' (PiLp.basisFun (p := (1 : ENNReal)) ℝ (Fin n) i)
          (PiLp.basisFun (p := (1 : ENNReal)) ℝ (Fin m) j)
    let maxEntry : ℝ := sSup { r : ℝ | ∃ i j, r = |AEntry i j| }
    OperatorNormDef A' =
        sSup { r : ℝ |
          ∃ x : (PiLp (1 : ENNReal) (fun _ : Fin n => ℝ)), ‖x‖ = 1 ∧ r = DualNormDef (A' x) } ∧
      OperatorNormDef A' = maxEntry ∧
      ((0 ≤ f xhat - φ uhat ∧
            f xhat - φ uhat ≤
              (4 * Real.sqrt (Real.log (n : ℝ) * Real.log (m : ℝ)) / ((N : ℝ) + 1)) *
                OperatorNormDef A') →
          0 ≤ f xhat - φ uhat ∧
            f xhat - φ uhat ≤
              (4 * Real.sqrt (Real.log (n : ℝ) * Real.log (m : ℝ)) / ((N : ℝ) + 1)) *
                maxEntry) := by
  classical
  dsimp
  set A' :
      (PiLp (1 : ENNReal) (fun _ : Fin n => ℝ)) →ₗ[ℝ]
        Module.Dual ℝ (PiLp (1 : ENNReal) (fun _ : Fin m => ℝ)) :=
    { toFun := fun x => (A x).toLinearMap
      map_add' := by
        intro x y
        ext u
        simp
      map_smul' := by
        intro r x
        ext u
        simp }
  set AEntry : Fin n → Fin m → ℝ :=
    fun i j =>
      A' (PiLp.basisFun (p := (1 : ENNReal)) ℝ (Fin n) i)
        (PiLp.basisFun (p := (1 : ENNReal)) ℝ (Fin m) j)
  set maxEntry : ℝ := sSup { r : ℝ | ∃ i j, r = |AEntry i j| }
  refine ⟨?_, ?_, ?_⟩
  · -- operator norm definition rewrite
    -- use the general lemma for continuous bilinear maps
    simpa [A', AEntry, maxEntry] using (operatorNormDef_eq_sSup_dualNormDef_of_continuous (A := A))
  · -- the max-entry formula in the ℓ1/ℓ∞ setup
    simpa [A', AEntry, maxEntry] using (operatorNormDef_eq_maxEntry_l1 (n := n) (m := m) A)
  · intro hgap
    refine ⟨hgap.1, ?_⟩
    -- substitute `OperatorNormDef A' = maxEntry` into the bound
    simpa [A', AEntry, maxEntry, (operatorNormDef_eq_maxEntry_l1 (n := n) (m := m) A)]
      using hgap.2

/- Proposition 1.4.1.1.
In the setting of Definition 1.4.1.2, take Euclidean norms on `ℝ^n` and `ℝ^m` and the
prox-functions `d1(x) = (1/2) ∑ (x^{(i)} - 1/n)^2` and `d2(u) = (1/2) ∑ (u^{(j)} - 1/m)^2` on
`Δ_n` and `Δ_m` (equations (4.7)–(4.8)). Then `σ1 = σ2 = 1`, `D1 = 1 - 1/n < 1`,
`D2 = 1 - 1/m < 1`, and `‖A‖_{1,2} = max_{‖x‖_1=1} ‖A x‖_2 = λ_max^{1/2}(A^T A)` (4.7).
Since `fhat(x) = ⟪c, x⟫_1` is linear, `M = 0` and Theorem 1.4.1 yields
`0 ≤ f(ĥx) - φ(ĥu) ≤ 4 λ_max^{1/2}(A^T A)/(N+1)` (4.11). -/
namespace matrixGame

open scoped BigOperators

/-- A coordinate of a point in the standard simplex is at most `1`. -/
lemma standardSimplex_coord_le_one {n : ℕ} {x : Fin n → ℝ} (hx : x ∈ standardSimplex n) :
    ∀ i, x i ≤ 1 := by
  classical
  intro i
  have hle : x i ≤ ∑ j, x j := by
    have hle' :
        x i ≤ ∑ j ∈ (Finset.univ : Finset (Fin n)), x j := by
      refine Finset.single_le_sum ?_ (by simp)
      intro j hj
      exact hx.1 j
    simpa using hle'
  calc
    x i ≤ ∑ j, x j := hle
    _ = (1 : ℝ) := hx.2

/-- A standard algebraic identity that simplifies the quadratic prox on the simplex. -/
lemma quadratic_prox_sumSq_identity (n : ℕ) (x : Fin n → ℝ) (hx : x ∈ standardSimplex n) :
    (∑ i, (x i - (1 / (n : ℝ))) ^ (2 : ℕ)) = (∑ i, (x i) ^ (2 : ℕ)) - (1 / (n : ℝ)) := by
  classical
  set a : ℝ := (1 / (n : ℝ))
  have hsum : (∑ i, x i) = (1 : ℝ) := hx.2
  have hExpand :
      (∑ i, (x i - a) ^ (2 : ℕ)) =
        (∑ i, (x i) ^ (2 : ℕ)) - (2 * a) * (∑ i, x i) + (n : ℝ) * a ^ (2 : ℕ) := by
    calc
      (∑ i, (x i - a) ^ (2 : ℕ)) = ∑ i, ((x i) ^ (2 : ℕ) - (2 * a) * x i + a ^ (2 : ℕ)) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        -- expand the square
        simp [pow_two]
        ring
      _ =
          (∑ i, (x i) ^ (2 : ℕ)) - (2 * a) * (∑ i, x i) + (n : ℝ) * a ^ (2 : ℕ) := by
        simp [sub_eq_add_neg, Finset.sum_add_distrib, Finset.sum_mul, add_left_comm, add_comm,
          mul_comm]
  have hna : (n : ℝ) * a ^ (2 : ℕ) = a := by
    by_cases hn : n = 0
    · subst hn
      simp [a]
    · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      simp [a, hn', pow_two]
  calc
    (∑ i, (x i - (1 / (n : ℝ))) ^ (2 : ℕ)) = ∑ i, (x i - a) ^ (2 : ℕ) := by simp [a]
    _ = (∑ i, (x i) ^ (2 : ℕ)) - (2 * a) * (∑ i, x i) + (n : ℝ) * a ^ (2 : ℕ) := hExpand
    _ = (∑ i, (x i) ^ (2 : ℕ)) - a := by
      -- use `∑ i, x i = 1` and `n * a^2 = a`
      simp [hsum, hna]
      ring
    _ = (∑ i, (x i) ^ (2 : ℕ)) - (1 / (n : ℝ)) := by simp [a]

/-- The squared sup norm on `Fin n → ℝ` is bounded by the sum of squared coordinates. -/
lemma norm_sq_le_sum_sq (n : ℕ) (z : Fin n → ℝ) :
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
      -- unpack `Pi`'s sup norm definition
      simp [Pi.norm_def, f, hsup]
    have hle' :
        ‖z i0‖ ^ (2 : ℕ) ≤ ∑ i, ‖z i‖ ^ (2 : ℕ) := by
      have hle'' :
          ‖z i0‖ ^ (2 : ℕ) ≤
            ∑ i ∈ (Finset.univ : Finset (Fin n)), ‖z i‖ ^ (2 : ℕ) := by
        refine
          Finset.single_le_sum (s := (Finset.univ : Finset (Fin n)))
            (f := fun i => ‖z i‖ ^ (2 : ℕ)) ?_ hi0
        intro i hi
        -- nonnegativity of squares
        exact pow_two_nonneg ‖z i‖
      -- turn the `Finset.univ` sum into the `Fintype` sum
      simpa using hle''
    calc
      ‖z‖ ^ (2 : ℕ) = ‖z i0‖ ^ (2 : ℕ) := by simp [hnorm]
      _ ≤ ∑ i, ‖z i‖ ^ (2 : ℕ) := hle'
      _ = ∑ i, (z i) ^ (2 : ℕ) := by
        simp [Real.norm_eq_abs]

/-- The quadratic prox-function has prox-diameter bounded by `1 - 1/n` on the standard simplex. -/
lemma quadratic_prox_diameter_bound (n : ℕ) :
    IsProxDiameterBound (standardSimplex n)
      (fun x : Fin n → ℝ => (1 / 2 : ℝ) * ∑ i, (x i - (1 / (n : ℝ))) ^ (2 : ℕ))
      (1 - 1 / (n : ℝ)) := by
  classical
  intro x hx
  by_cases hn : n = 0
  · subst hn
    simp [standardSimplex] at hx
  · have hxle : ∀ i, x i ≤ 1 := standardSimplex_coord_le_one (hx := hx)
    have hsq_le :
        (∑ i, (x i) ^ (2 : ℕ)) ≤ ∑ i, x i := by
      refine Finset.sum_le_sum ?_
      intro i hi
      have h0 : 0 ≤ x i := hx.1 i
      have h1 : x i ≤ 1 := hxle i
      -- `x_i^2 ≤ x_i` for `0 ≤ x_i ≤ 1`
      have : x i * x i ≤ x i * (1 : ℝ) := mul_le_mul_of_nonneg_left h1 h0
      simpa [pow_two, mul_assoc] using this
    have hsq_le_one : (∑ i, (x i) ^ (2 : ℕ)) ≤ 1 := by
      simpa [hx.2] using hsq_le
    have hid := quadratic_prox_sumSq_identity (n := n) x hx
    have hD1_nonneg : 0 ≤ (1 - 1 / (n : ℝ)) := by
      have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      have hn1 : (1 : ℝ) / (n : ℝ) ≤ 1 := by
        have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
        simpa [one_div] using (inv_le_one_of_one_le₀ (by exact_mod_cast hnpos))
      linarith
    -- first bound by the tighter `(1/2) * (1 - 1/n)`, then relax to `1 - 1/n`
    have hTight :
        (1 / 2 : ℝ) * ∑ i, (x i - (1 / (n : ℝ))) ^ (2 : ℕ) ≤
          (1 / 2 : ℝ) * (1 - 1 / (n : ℝ)) := by
      have hsq_sub :
          ∑ i, (x i - (1 / (n : ℝ))) ^ (2 : ℕ) ≤
            (1 - 1 / (n : ℝ)) := by
        -- use the identity and `∑ x_i^2 ≤ 1`
        have hEq :
            (∑ i, (x i - (1 / (n : ℝ))) ^ (2 : ℕ)) =
              (∑ i, (x i) ^ (2 : ℕ)) - (1 / (n : ℝ)) := hid
        have h1 :
            (∑ i, (x i - (1 / (n : ℝ))) ^ (2 : ℕ)) ≤
              (∑ i, (x i) ^ (2 : ℕ)) - (1 / (n : ℝ)) :=
          le_of_eq hEq
        have h2 : (∑ i, (x i) ^ (2 : ℕ)) - (1 / (n : ℝ)) ≤ 1 - (1 / (n : ℝ)) := by
          linarith [hsq_le_one]
        exact h1.trans h2
      exact mul_le_mul_of_nonneg_left hsq_sub (by norm_num)
    have hRelax :
        (1 / 2 : ℝ) * (1 - 1 / (n : ℝ)) ≤ 1 - 1 / (n : ℝ) := by
      have : (1 / 2 : ℝ) ≤ 1 := by norm_num
      simpa [one_mul] using mul_le_mul_of_nonneg_right this hD1_nonneg
    exact le_trans hTight hRelax

/-- The quadratic prox-function is `1`-strongly convex on the standard simplex. -/
lemma quadratic_prox_strongConvexOn (n : ℕ) :
    StrongConvexOn (standardSimplex n) 1
      (fun x : Fin n → ℝ => (1 / 2 : ℝ) * ∑ i, (x i - (1 / (n : ℝ))) ^ (2 : ℕ)) := by
  classical
  -- unfold `StrongConvexOn` and provide convexity and the strong convexity inequality
  unfold StrongConvexOn
  refine ⟨?_, ?_⟩
  · simpa [standardSimplex_eq_stdSimplex] using (convex_stdSimplex ℝ (Fin n))
  · intro x hx y hy a b ha hb hab
    set a0 : ℝ := (1 / (n : ℝ))
    set d : (Fin n → ℝ) → ℝ :=
      fun z => (1 / 2 : ℝ) * ∑ i, (z i - a0) ^ (2 : ℕ)
    have hb' : b = 1 - a := by linarith [hab]
    have hsum :
        ∑ i, ((a • x + b • y) i - a0) ^ (2 : ℕ) =
          a * ∑ i, (x i - a0) ^ (2 : ℕ) +
              b * ∑ i, (y i - a0) ^ (2 : ℕ) -
            a * b * ∑ i, (x i - y i) ^ (2 : ℕ) := by
      -- prove the identity coordinatewise and sum it up
      have hcoord :
          ∀ i : Fin n,
            ((a • x + b • y) i - a0) ^ (2 : ℕ) =
              a * (x i - a0) ^ (2 : ℕ) + b * (y i - a0) ^ (2 : ℕ) -
                a * b * (x i - y i) ^ (2 : ℕ) := by
        intro i
        subst hb'
        -- polynomial identity in one dimension, using `a + (1-a) = 1`
        simp [a0, pow_two, smul_eq_mul]
        ring
      have hsum' :
          (∑ i, ((a • x + b • y) i - a0) ^ (2 : ℕ)) =
            ∑ i, (a * (x i - a0) ^ (2 : ℕ) + b * (y i - a0) ^ (2 : ℕ) -
              a * b * (x i - y i) ^ (2 : ℕ)) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        simpa using hcoord i
      -- now simplify the sum using linearity
      simpa [sub_eq_add_neg, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul, add_assoc,
        add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using hsum'
    have hnormSq :
        ‖x - y‖ ^ (2 : ℕ) ≤ ∑ i, (x i - y i) ^ (2 : ℕ) := by
      simpa [Pi.sub_apply] using norm_sq_le_sum_sq (n := n) (z := x - y)
    have hcoef_nonneg : 0 ≤ a * b * ((1 : ℝ) / 2 * ‖x - y‖ ^ 2) := by
      have : 0 ≤ (1 : ℝ) / 2 * ‖x - y‖ ^ 2 := by positivity
      exact mul_nonneg (mul_nonneg ha hb) this
    -- use the exact quadratic identity and relax `∑ (x-y)^2` to `‖x-y‖^2`
    have hgap :
        a * b * ((1 : ℝ) / 2 * ‖x - y‖ ^ 2) ≤
          a * b * ((1 : ℝ) / 2 * ∑ i, (x i - y i) ^ (2 : ℕ)) := by
      have hcoef : 0 ≤ a * b * ((1 : ℝ) / 2) := by
        exact mul_nonneg (mul_nonneg ha hb) (by norm_num)
      -- rewrite `‖x-y‖^2` as `‖x-y‖^(2:ℕ)` to use `hnormSq`
      have hnormSq' : (‖x - y‖ ^ (2 : ℕ)) ≤ ∑ i, (x i - y i) ^ (2 : ℕ) := hnormSq
      have : ((1 : ℝ) / 2) * ‖x - y‖ ^ (2 : ℕ) ≤ ((1 : ℝ) / 2) * ∑ i, (x i - y i) ^ (2 : ℕ) := by
        exact mul_le_mul_of_nonneg_left hnormSq' (by norm_num)
      -- adjust the exponent `‖x-y‖^2` vs `‖x-y‖^(2:ℕ)`
      have : ((1 : ℝ) / 2 * ‖x - y‖ ^ 2) ≤ ((1 : ℝ) / 2 * ∑ i, (x i - y i) ^ (2 : ℕ)) := by
        simpa [pow_two] using this
      exact mul_le_mul_of_nonneg_left this (mul_nonneg ha hb)
    -- assemble
    have hd_exact :
        d (a • x + b • y) =
          a * d x + b * d y - a * b * ((1 : ℝ) / 2 * ∑ i, (x i - y i) ^ (2 : ℕ)) := by
      -- use `hsum`, then distribute the scalar factors
      set SX : ℝ := ∑ i, (x i - a0) ^ (2 : ℕ)
      set SY : ℝ := ∑ i, (y i - a0) ^ (2 : ℕ)
      set SD : ℝ := ∑ i, (x i - y i) ^ (2 : ℕ)
      have hsumSX :
          ∑ i, ((a • x + b • y) i - a0) ^ (2 : ℕ) = a * SX + b * SY - a * b * SD := by
        simpa [SX, SY, SD] using hsum
      have hsumSX' :
          (∑ i, (a * x i + b * y i - a0) ^ (2 : ℕ)) = a * SX + b * SY - a * b * SD := by
        simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hsumSX
      have hd1 :
          d (a • x + b • y) = (1 / 2 : ℝ) * (a * SX + b * SY - a * b * SD) := by
        simp [d, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hsumSX']
      -- now rewrite `d x` and `d y` and finish by ring
      calc
        d (a • x + b • y) = (1 / 2 : ℝ) * (a * SX + b * SY - a * b * SD) := hd1
        _ = a * ((1 / 2 : ℝ) * SX) + b * ((1 / 2 : ℝ) * SY) - a * b * ((1 / 2 : ℝ) * SD) := by
          ring
        _ = a * d x + b * d y - a * b * ((1 / 2 : ℝ) * SD) := by
          simp [d, SX, SY]
        _ = a * d x + b * d y - a * b * ((1 : ℝ) / 2 * ∑ i, (x i - y i) ^ (2 : ℕ)) := by
          simp [SD, div_eq_mul_inv]
    -- the inequality demanded by `UniformConvexOn`
    -- note `a • d x = a * d x` in `ℝ`
    have :
        d (a • x + b • y) ≤ a * d x + b * d y - a * b * ((1 : ℝ) / 2 * ‖x - y‖ ^ 2) := by
      -- use the exact identity and monotonicity of subtraction
      have :
          a * d x + b * d y - a * b * ((1 : ℝ) / 2 * ∑ i, (x i - y i) ^ (2 : ℕ)) ≤
            a * d x + b * d y - a * b * ((1 : ℝ) / 2 * ‖x - y‖ ^ 2) := by
        -- `X ≤ Y` implies `A - Y ≤ A - X`; use `hgap` in that direction
        have hgap' :
            a * b * ((1 : ℝ) / 2 * ‖x - y‖ ^ 2) ≤
              a * b * ((1 : ℝ) / 2 * ∑ i, (x i - y i) ^ (2 : ℕ)) := by
          -- same as `hgap` but with the `1/2` moved inside
          simpa [mul_assoc, mul_left_comm, mul_comm] using hgap
        exact sub_le_sub_left hgap' (a * d x + b * d y)
      -- conclude
      simpa [hd_exact] using this
    -- rewrite back to the original `let`-function
    simpa [d, a0, d, smul_eq_mul] using this

/-- `DualNormDef` is nonnegative. -/
lemma dualNormDef_nonneg {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (s : Module.Dual ℝ E) : 0 ≤ DualNormDef s := by
  classical
  set S : Set ℝ := { r : ℝ | ∃ x : E, ‖x‖ = 1 ∧ r = DualPairing s x } with hSdef
  have hDual : DualNormDef s = sSup S := by
    unfold DualNormDef
    rw [hSdef.symm]
  by_cases hS : S = ∅
  · have : DualNormDef s = 0 := by simp [hDual, hS, Real.sSup_empty]
    simp [this]
  · have hSne : S.Nonempty := Set.nonempty_iff_ne_empty.2 hS
    rcases hSne with ⟨r, hr⟩
    have hneg : (-r) ∈ S := by
      rcases hr with ⟨x, hx, rfl⟩
      refine ⟨-x, ?_, ?_⟩
      · simpa [norm_neg] using hx
      · simp [DualPairing]
    have hex : ∃ t ∈ S, 0 ≤ t := by
      by_cases hr0 : 0 ≤ r
      · exact ⟨r, hr, hr0⟩
      · have : 0 ≤ -r := by linarith
        exact ⟨-r, hneg, this⟩
    have : 0 ≤ sSup S := Real.sSup_nonneg' hex
    simpa [hDual] using this

set_option maxHeartbeats 400000 in
/-- For the linear map `A'` induced from `A`, `OperatorNormDef` is the supremum of `DualNormDef`
over unit vectors. -/
lemma operatorNormDef_eq_sSup_dualNormDef (n m : ℕ)
    (A : (Fin n → ℝ) →L[ℝ] ((Fin m → ℝ) →L[ℝ] ℝ)) :
    let A' : (Fin n → ℝ) →ₗ[ℝ] Module.Dual ℝ (Fin m → ℝ) :=
      { toFun := fun x => (A x).toLinearMap
        map_add' := by
          intro x y
          ext u
          simp
        map_smul' := by
          intro r x
          ext u
          simp }
    OperatorNormDef A' =
      sSup { r : ℝ | ∃ x : (Fin n → ℝ), ‖x‖ = 1 ∧ r = DualNormDef (A' x) } := by
  classical
  intro A'
  -- auxiliary sets from the definitions
  set S : Set ℝ :=
      { r : ℝ |
        ∃ x : (Fin n → ℝ), ∃ u : (Fin m → ℝ), ‖x‖ = 1 ∧ ‖u‖ = 1 ∧ r = DualPairing (A' x) u }
  set T : Set ℝ :=
      { r : ℝ | ∃ x : (Fin n → ℝ), ‖x‖ = 1 ∧ r = DualNormDef (A' x) }
  have hOp : OperatorNormDef A' = sSup S := by
    simp [OperatorNormDef, S]
  have hSbdd : BddAbove S := by
    refine ⟨‖A‖, ?_⟩
    rintro r ⟨x, u, hx, hu, rfl⟩
    have h0 : (A x u) ≤ ‖A x u‖ := by
      simpa [Real.norm_eq_abs] using (le_abs_self (A x u))
    have h1 : ‖A x u‖ ≤ ‖A x‖ * ‖u‖ := by
      simpa using (A x).le_opNorm u
    have h2 : ‖A x‖ ≤ ‖A‖ * ‖x‖ := by
      simpa using A.le_opNorm x
    have h1' : ‖A x u‖ ≤ ‖A x‖ := by
      simpa [hu] using h1
    have h3 : ‖A x‖ ≤ ‖A‖ := by
      simpa [hx] using h2
    have h4 : ‖A x u‖ ≤ ‖A‖ := h1'.trans h3
    exact h0.trans h4
  have hT_nonneg : 0 ≤ sSup T := by
    by_cases hT : T = ∅
    · simp [hT, Real.sSup_empty]
    · have hTne : T.Nonempty := Set.nonempty_iff_ne_empty.2 hT
      rcases hTne with ⟨r, hr⟩
      rcases hr with ⟨x, hx, rfl⟩
      have : 0 ≤ DualNormDef (A' x) := dualNormDef_nonneg (s := A' x)
      -- `DualNormDef (A' x)` is a nonnegative element of `T`
      refine Real.sSup_nonneg' ?_
      refine ⟨DualNormDef (A' x), ?_, this⟩
      exact ⟨x, hx, rfl⟩
  have hST : sSup S ≤ sSup T := by
    refine Real.sSup_le ?_ hT_nonneg
    intro r hr
    rcases hr with ⟨x, u, hx, hu, rfl⟩
    -- bound `⟪A' x, u⟫` by the corresponding dual norm, then by `sSup T`
    set Sx : Set ℝ := { r : ℝ | ∃ v : (Fin m → ℝ), ‖v‖ = 1 ∧ r = DualPairing (A' x) v }
    have hSx_bdd : BddAbove Sx := by
      refine ⟨‖A x‖, ?_⟩
      rintro r ⟨v, hv, rfl⟩
      have h0 : (A x v) ≤ ‖A x v‖ := by
        simpa [Real.norm_eq_abs] using (le_abs_self (A x v))
      have h1 : ‖A x v‖ ≤ ‖A x‖ * ‖v‖ := by
        simpa using (A x).le_opNorm v
      have h2 : ‖A x v‖ ≤ ‖A x‖ := by
        simpa [hv] using h1
      exact h0.trans h2
    have hmemSx : DualPairing (A' x) u ∈ Sx := ⟨u, hu, rfl⟩
    have hle_dual : DualPairing (A' x) u ≤ DualNormDef (A' x) := by
      -- unfold `DualNormDef` and use `le_csSup`
      simpa [DualNormDef, Sx] using (le_csSup hSx_bdd hmemSx)
    have hT_bdd : BddAbove T := by
      refine ⟨‖A‖, ?_⟩
      rintro r ⟨x, hx, rfl⟩
      -- `DualNormDef (A' x) ≤ ‖A x‖ ≤ ‖A‖`
      have hdual_le : DualNormDef (A' x) ≤ ‖A x‖ := by
        unfold DualNormDef
        -- bound each element in the defining set by `‖A x‖`
        refine Real.sSup_le ?_ (norm_nonneg (A x))
        intro r hr
        rcases hr with ⟨v, hv, rfl⟩
        have h0 : (A x v) ≤ ‖A x v‖ := by
          simpa [Real.norm_eq_abs] using (le_abs_self (A x v))
        have h1 : ‖A x v‖ ≤ ‖A x‖ * ‖v‖ := by
          simpa using (A x).le_opNorm v
        have h2 : ‖A x v‖ ≤ ‖A x‖ := by
          simpa [hv] using h1
        exact h0.trans h2
      have hAx_le : ‖A x‖ ≤ ‖A‖ * ‖x‖ := by
        simpa using A.le_opNorm x
      have hAx_le' : ‖A x‖ ≤ ‖A‖ := by
        simpa [hx] using hAx_le
      exact hdual_le.trans hAx_le'
    have hle_sSupT : DualNormDef (A' x) ≤ sSup T := by
      exact le_csSup hT_bdd ⟨x, hx, rfl⟩
    exact le_trans hle_dual hle_sSupT
  have hTS : sSup T ≤ sSup S := by
    have hS_nonneg : 0 ≤ sSup S := by
      simpa [hOp] using (operatorNormDef_nonneg (A := A'))
    refine Real.sSup_le ?_ hS_nonneg
    intro r hr
    rcases hr with ⟨x, hx, rfl⟩
    -- show `DualNormDef (A' x) ≤ sSup S` by bounding each element of its defining set
    unfold DualNormDef
    refine Real.sSup_le ?_ hS_nonneg
    intro t ht
    rcases ht with ⟨u, hu, rfl⟩
    have hmemS : DualPairing (A' x) u ∈ S := ⟨x, u, hx, hu, rfl⟩
    exact le_csSup hSbdd hmemS
  exact le_antisymm (by simpa [hOp] using hST) (by simpa [hOp] using hTS)

/-- For a positive natural `k`, the value `1 - 1/k` is nonnegative. -/
lemma D_nonneg (k : ℕ) (hk : k ≠ 0) : 0 ≤ (1 : ℝ) - 1 / (k : ℝ) := by
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk
  have hk1 : (1 : ℕ) ≤ k := (Nat.succ_le_iff).2 hkpos
  have hk1' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  have hle : (1 / (k : ℝ)) ≤ 1 := by
    simpa [one_div] using (inv_le_one_of_one_le₀ hk1')
  exact sub_nonneg.2 hle

/-- If `a, b ∈ [0, 1]`, then `Real.sqrt (a * b) ≤ 1`. -/
lemma sqrt_mul_le_one_of_le_one {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b)
    (hb1 : b ≤ 1) : Real.sqrt (a * b) ≤ 1 := by
  have hab_le_left : a * b ≤ a := by
    have h := mul_le_mul_of_nonneg_left hb1 ha0
    simpa [mul_one] using h
  have hab_le_right : a * b ≤ b := by
    have h := mul_le_mul_of_nonneg_right ha1 hb0
    simpa [one_mul] using h
  have hab : a * b ≤ 1 :=
    (le_min hab_le_left hab_le_right).trans ((min_le_left a b).trans ha1)
  exact (Real.sqrt_le_one).2 hab

/-- Simplify a Theorem 1.4.1-style duality-gap bound in the Euclidean simplex setup (`M = 0`). -/
lemma duality_gap_simplify_from_thm141_M0 {gap op lambdaMax D1 D2 : ℝ} (N : ℕ)
    (hop : op = Real.sqrt lambdaMax) (hop_nonneg : 0 ≤ op) (hD1_0 : 0 ≤ D1) (hD1_1 : D1 ≤ 1)
    (hD2_0 : 0 ≤ D2) (hD2_1 : D2 ≤ 1)
    (hgap : gap ≤ (4 * op) / ((N : ℝ) + 1) * Real.sqrt (D1 * D2)) :
    gap ≤ (4 * Real.sqrt lambdaMax) / ((N : ℝ) + 1) := by
  have hsqrt : Real.sqrt (D1 * D2) ≤ 1 :=
    sqrt_mul_le_one_of_le_one hD1_0 hD1_1 hD2_0 hD2_1
  have hden_pos : 0 < (N : ℝ) + 1 := by positivity
  have hfac_nonneg : 0 ≤ (4 * op) / ((N : ℝ) + 1) := by
    have hnum_nonneg : 0 ≤ 4 * op := by nlinarith
    exact div_nonneg hnum_nonneg (le_of_lt hden_pos)
  have hmul :
      (4 * op) / ((N : ℝ) + 1) * Real.sqrt (D1 * D2) ≤ (4 * op) / ((N : ℝ) + 1) := by
    simpa [mul_one] using (mul_le_mul_of_nonneg_left hsqrt hfac_nonneg)
  have hle : gap ≤ (4 * op) / ((N : ℝ) + 1) := le_trans hgap hmul
  simpa [hop] using hle

end matrixGame

end Section04Part7

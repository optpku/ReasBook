/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Definition_13_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators

section

/- `prompt_add/` is absent in this workspace, so the design review is done against mathlib, the
nearby scalar-recurrence items `Chap10/Lemma_10_70` and `Chap11/Lemma_11_7`, and the Chapter 13
stepsize owner `conditional_gradient_predefined_diminishing_stepsize` from Definition 13.6. This
item is `source-facing`: it is a decay estimate for two scalar sequences `a, b : ℕ → ℝ` indexed
by `ℕ`, with the half-tail range in part `(b)` naturally represented by `Set.Icc (k / 2 + 2) k`.
The owner abstraction is therefore still the plain sequence type `ℕ → ℝ`. The primitive data is
the recurrence itself together with the integer shift parameter `p`; the rate bounds are derived
API. Under `hp : 1 ≤ p`, the shifted owner
`conditional_gradient_predefined_diminishing_stepsize (k + 2 * (p - 1))` is exactly the textbook
scalar `2 / (k + 2 * p)`, so the recurrence input is stated directly with that existing owner
instead of repeating a parallel raw stepsize formula. -/

variable (a b : ℕ → ℝ) (A : ℝ) (p : ℕ)

variable (hp : 1 ≤ p)
variable (ha_nonneg : ∀ k : ℕ, 0 ≤ a k)
variable
  (hstep : ∀ k : ℕ,
    a (k + 1) ≤
      a k
        - conditional_gradient_predefined_diminishing_stepsize (k + 2 * (p - 1)) * b k +
        (A / 2) *
          (conditional_gradient_predefined_diminishing_stepsize (k + 2 * (p - 1))) ^ (2 : ℕ))
variable (ha_le_b : ∀ k : ℕ, a k ≤ b k)

/-- Helper for Lemma 13.13: shifting the predefined diminishing stepsize by `2 (p - 1)`
reproduces the textbook factor `2 / (n + 2p)`. -/
lemma shifted_conditional_gradient_stepsize_eq (hp : 1 ≤ p) (n : ℕ) :
    conditional_gradient_predefined_diminishing_stepsize (n + 2 * (p - 1)) =
      2 / (n + 2 * p : ℝ) := by
  -- Rewrite the owner formula and normalize the shifted index with `hp`.
  have hp' : 1 ≤ p := hp
  have hshift : n + (2 * (p - 1) + 2) = n + 2 * p := by
    omega
  have hshift_cast : (((n + 2 * (p - 1) + 2 : ℕ) : ℝ)) = ((n + 2 * p : ℕ) : ℝ) := by
    exact_mod_cast hshift
  rw [conditional_gradient_predefined_diminishing_stepsize_eq]
  simpa using congrArg (fun t : ℝ ↦ 2 / t) hshift_cast

/-- Helper for Lemma 13.13: the control constant `max {A, (p - 1) a₀}` is nonnegative. -/
lemma scalar_recurrence_control_nonneg (ha_nonneg : ∀ k : ℕ, 0 ≤ a k) :
    0 ≤ max A ((((p - 1 : ℕ) : ℝ) * a 0)) := by
  -- The second branch is nonnegative because both factors are.
  refine le_trans ?_ (le_max_right A ((((p - 1 : ℕ) : ℝ) * a 0)))
  exact mul_nonneg (Nat.cast_nonneg (p - 1)) (ha_nonneg 0)

/-- Helper for Lemma 13.13: multiplying the one-step recurrence by
`(n + 2p - 1)(n + 2p)` yields the weighted increment bound needed for telescoping. -/
lemma weighted_scalar_recurrence_step
    (hp : 1 ≤ p)
    (ha_nonneg : ∀ k : ℕ, 0 ≤ a k)
    (hstep : ∀ k : ℕ,
      a (k + 1) ≤
        a k
          - conditional_gradient_predefined_diminishing_stepsize (k + 2 * (p - 1)) * b k +
          (A / 2) *
            (conditional_gradient_predefined_diminishing_stepsize (k + 2 * (p - 1))) ^ (2 : ℕ))
    (ha_le_b : ∀ k : ℕ, a k ≤ b k)
    (n : ℕ) :
    (((n + 2 * p - 1 : ℕ) : ℝ) * (((n + 2 * p : ℕ) : ℝ)) * a (n + 1)) ≤
      (((n + 2 * p - 2 : ℕ) : ℝ) * (((n + 2 * p - 1 : ℕ) : ℝ)) * a n +
        2 * max A ((((p - 1 : ℕ) : ℝ) * a 0))) := by
  let d : ℝ := ((n + 2 * p : ℕ) : ℝ)
  let u : ℝ := ((n + 2 * p - 1 : ℕ) : ℝ)
  let v : ℝ := ((n + 2 * p - 2 : ℕ) : ℝ)
  have hd_pos : 0 < d := by
    dsimp [d]
    positivity
  have hu_nonneg : 0 ≤ u := by
    dsimp [u]
    positivity
  have hw_nonneg : 0 ≤ u * d := mul_nonneg hu_nonneg hd_pos.le
  have hu_eq : u = d - 1 := by
    have hnat : 1 ≤ n + 2 * p := by
      omega
    dsimp [u, d]
    rw [show ((n + 2 * p - 1 : ℕ) : ℝ) = ((n + 2 * p : ℕ) : ℝ) - 1 by
      norm_num [Nat.cast_sub hnat]]
  have hv_eq : v = d - 2 := by
    have hnat : 2 ≤ n + 2 * p := by
      omega
    dsimp [v, d]
    rw [show ((n + 2 * p - 2 : ℕ) : ℝ) = ((n + 2 * p : ℕ) : ℝ) - 2 by
      norm_num [Nat.cast_sub hnat]]
  have hu_le_d : u ≤ d := by
    nlinarith [hu_eq, hd_pos]
  have hratio_nonneg : 0 ≤ u / d := by
    positivity
  have hratio_le_one : u / d ≤ 1 := by
    exact (div_le_iff₀ hd_pos).2 (by simpa using hu_le_d)
  have hstep' := hstep n
  rw [shifted_conditional_gradient_stepsize_eq (p := p) hp n] at hstep'
  have hstep_mul :
      u * d * a (n + 1) ≤
        u * d * (a n - (2 / d) * b n + (A / 2) * (2 / d) ^ (2 : ℕ)) := by
    simpa [d] using mul_le_mul_of_nonneg_left hstep' hw_nonneg
  have hexpand :
      u * d * (a n - (2 / d) * b n + (A / 2) * (2 / d) ^ (2 : ℕ)) =
        u * d * a n - 2 * u * b n + 2 * A * (u / d) := by
    -- Clear the common denominator `d` once to expose the weighted coefficients.
    rw [pow_two]
    field_simp [hd_pos.ne']
  have hcontract :
      u * d * a n - 2 * u * a n = v * u * a n := by
    -- The special stepsize makes the coefficient collapse from `d - 2` to `v`.
    calc
      u * d * a n - 2 * u * a n = u * (d - 2) * a n := by ring
      _ = u * v * a n := by rw [hv_eq]
      _ = v * u * a n := by ring
  have hneg_term :
      u * d * a n - 2 * u * b n ≤ u * d * a n - 2 * u * a n := by
    -- Replace `b n` by the smaller quantity `a n` inside the dissipative term.
    nlinarith [ha_le_b n, hu_nonneg]
  have herror_bound :
      2 * A * (u / d) ≤ 2 * max A ((((p - 1 : ℕ) : ℝ) * a 0)) := by
    have hmax_nonneg :
        0 ≤ max A ((((p - 1 : ℕ) : ℝ) * a 0)) :=
      scalar_recurrence_control_nonneg (a := a) (A := A) (p := p) ha_nonneg
    by_cases hA_nonneg : 0 ≤ A
    · have hA_le :
          A ≤ max A ((((p - 1 : ℕ) : ℝ) * a 0)) := le_max_left _ _
      have hratio_bound : A * (u / d) ≤ A := by
        nlinarith
      nlinarith
    · have hA_nonpos : A ≤ 0 := le_of_not_ge hA_nonneg
      nlinarith
  calc
    (((n + 2 * p - 1 : ℕ) : ℝ) * (((n + 2 * p : ℕ) : ℝ)) * a (n + 1))
        = u * d * a (n + 1) := by simp [u, d, mul_assoc]
    _ ≤ u * d * (a n - (2 / d) * b n + (A / 2) * (2 / d) ^ (2 : ℕ)) := hstep_mul
    _ = u * d * a n - 2 * u * b n + 2 * A * (u / d) := hexpand
    _ ≤ u * d * a n - 2 * u * a n + 2 * max A ((((p - 1 : ℕ) : ℝ) * a 0)) := by
      linarith
    _ = v * u * a n + 2 * max A ((((p - 1 : ℕ) : ℝ) * a 0)) := by
      rw [hcontract]
    _ = ((((n + 2 * p - 2 : ℕ) : ℝ) * (((n + 2 * p - 1 : ℕ) : ℝ)) * a n) +
          2 * max A ((((p - 1 : ℕ) : ℝ) * a 0))) := by
      simp [u, v, mul_comm]

/-- Helper for Lemma 13.13: iterating the weighted one-step estimate bounds the whole weighted
trajectory by the initial weighted value plus `2M` per iteration. -/
lemma weighted_scalar_recurrence_bound
    (hp : 1 ≤ p)
    (ha_nonneg : ∀ k : ℕ, 0 ≤ a k)
    (hstep : ∀ k : ℕ,
      a (k + 1) ≤
        a k
          - conditional_gradient_predefined_diminishing_stepsize (k + 2 * (p - 1)) * b k +
          (A / 2) *
            (conditional_gradient_predefined_diminishing_stepsize (k + 2 * (p - 1))) ^ (2 : ℕ))
    (ha_le_b : ∀ k : ℕ, a k ≤ b k)
    (n : ℕ) :
    ((((n + 2 * p - 2 : ℕ) : ℝ) * (((n + 2 * p - 1 : ℕ) : ℝ))) * a n) ≤
      ((((2 * p - 2 : ℕ) : ℝ) * (((2 * p - 1 : ℕ) : ℝ))) * a 0) +
        2 * max A ((((p - 1 : ℕ) : ℝ) * a 0)) * n := by
  induction n with
  | zero =>
      -- The weighted bound starts from the exact initial weighted value.
      simp
  | succ n ihn =>
      -- Advance the weighted estimate by one step and absorb the new `2M` increment.
      have hstep_weighted :=
        weighted_scalar_recurrence_step
          (a := a) (b := b) (A := A) (p := p) hp ha_nonneg hstep ha_le_b n
      calc
        ((((n + 1 + 2 * p - 2 : ℕ) : ℝ) * (((n + 1 + 2 * p - 1 : ℕ) : ℝ))) * a (n + 1))
            ≤ ((((n + 2 * p - 2 : ℕ) : ℝ) * (((n + 2 * p - 1 : ℕ) : ℝ)) * a n) +
                2 * max A ((((p - 1 : ℕ) : ℝ) * a 0))) := by
              have hleft : n + 1 + 2 * p - 2 = n + 2 * p - 1 := by
                omega
              have hright : n + 1 + 2 * p - 1 = n + 2 * p := by
                omega
              simpa [hleft, hright] using hstep_weighted
        _ ≤ ((((2 * p - 2 : ℕ) : ℝ) * (((2 * p - 1 : ℕ) : ℝ))) * a 0) +
              2 * max A ((((p - 1 : ℕ) : ℝ) * a 0)) * n +
              2 * max A ((((p - 1 : ℕ) : ℝ) * a 0)) := by
            linarith
        _ = ((((2 * p - 2 : ℕ) : ℝ) * (((2 * p - 1 : ℕ) : ℝ))) * a 0) +
              2 * max A ((((p - 1 : ℕ) : ℝ) * a 0)) * ((n : ℝ) + 1) := by
            ring
        _ = ((((2 * p - 2 : ℕ) : ℝ) * (((2 * p - 1 : ℕ) : ℝ))) * a 0) +
              2 * max A ((((p - 1 : ℕ) : ℝ) * a 0)) * (((n + 1 : ℕ) : ℝ)) := by
            norm_num [Nat.cast_add]

include hp ha_nonneg hstep ha_le_b

-- Proof sketch: use `a k ≤ b k` to rewrite the recurrence as
-- `a (k + 1) ≤ (1 - γₖ) * a k + (A / 2) * γₖ²` with
-- `γₖ = conditional_gradient_predefined_diminishing_stepsize (k + 2 * (p - 1)) = 2 / (k + 2p)`,
-- then unroll the
-- recursion and estimate the resulting product and sum exactly as in the textbook.
/-- Lemma 13.13 (1): if nonnegative sequences `a_k` and `b_k` satisfy
`a_{k+1} ≤ a_k - γ_k b_k + (A / 2) γ_k^2` with `γ_k = 2 / (k + 2p)` and `a_k ≤ b_k`, then for
every `k ≥ 1` one has
`a_k ≤ 2 * max {A, (p - 1) a_0} / (k + 2p - 2)`. -/
theorem scalar_recurrence_le_sublinear_bound_of_conditional_gradient_stepsize
    {k : ℕ} (hk : 1 ≤ k) :
    a k ≤
      (2 * max A ((((p - 1 : ℕ) : ℝ) * a 0))) /
        (((k + 2 * p - 2 : ℕ) : ℝ)) := by
  let M : ℝ := max A ((((p - 1 : ℕ) : ℝ) * a 0))
  let d : ℝ := ((k + 2 * p - 2 : ℕ) : ℝ)
  let e : ℝ := ((k + 2 * p - 1 : ℕ) : ℝ)
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    exact scalar_recurrence_control_nonneg (a := a) (A := A) (p := p) ha_nonneg
  have hd_pos : 0 < d := by
    dsimp [d]
    have hk_pos : 0 < k := by
      omega
    have hp_pos : 0 < p := by
      omega
    have hnat : 0 < k + (2 * p - 2) := by
      have htwo : 0 ≤ 2 * p - 2 := by
        omega
      omega
    have hrewrite : k + 2 * p - 2 = k + (2 * p - 2) := by
      omega
    rw [hrewrite]
    exact Nat.cast_pos.mpr hnat
  have he_pos : 0 < e := by
    dsimp [e]
    have hnat : 0 < k + 2 * p - 1 := by
      omega
    exact Nat.cast_pos.mpr hnat
  have hweighted :=
    weighted_scalar_recurrence_bound
      (a := a) (b := b) (A := A) (p := p) hp ha_nonneg hstep ha_le_b k
  have hinitial :
      ((((2 * p - 2 : ℕ) : ℝ) * (((2 * p - 1 : ℕ) : ℝ))) * a 0) ≤
        2 * M * (((2 * p - 1 : ℕ) : ℝ)) := by
    -- Control the initial weighted term by the same constant `M`.
    have hM_ge :
        (((p - 1 : ℕ) : ℝ) * a 0) ≤ M := by
      dsimp [M]
      exact le_max_right _ _
    have hfactor : (((2 * p - 2 : ℕ) : ℝ)) = 2 * (((p - 1 : ℕ) : ℝ)) := by
      exact_mod_cast (show 2 * p - 2 = 2 * (p - 1) by omega)
    have htail_nonneg : 0 ≤ (((2 * p - 1 : ℕ) : ℝ)) := by
      positivity
    rw [hfactor]
    nlinarith [hM_ge, ha_nonneg 0, htail_nonneg]
  have hmain :
      d * e * a k ≤ 2 * M * e := by
    -- Combine the telescoped invariant with the initial-term estimate.
    have hsplit_e : (((2 * p - 1 : ℕ) : ℝ)) + (k : ℝ) = e := by
      dsimp [e]
      have hnat : 2 * p - 1 + k = k + 2 * p - 1 := by
        omega
      exact_mod_cast hnat
    dsimp [d, e, M] at hweighted hinitial ⊢
    nlinarith [hweighted, hinitial, hsplit_e]
  have hcancel_e : d * a k ≤ 2 * M := by
    have hmain' : e * (d * a k) ≤ e * (2 * M) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hmain
    exact le_of_mul_le_mul_left hmain' he_pos
  have hcancel_d : a k * d ≤ 2 * M := by
    simpa [mul_comm] using hcancel_e
  -- Cancel the final positive denominator to recover the claimed bound.
  have hresult : a k ≤ (2 * M) / d := by
    exact (le_div_iff₀ hd_pos).2 hcancel_d
  dsimp [M, d] at hresult ⊢
  simpa using hresult

include hp

-- Proof sketch: sum the recurrence from `n = j` to `n = k`, bound `a j` by part `(1)`, estimate
-- the quadratic remainder by a telescoping series, and then choose `j = k / 2 + 2` to obtain the
-- half-tail bound. On a finite nonempty interval, this is equivalent to the textbook estimate on
-- the minimum of the `b_n`.
omit ha_nonneg ha_le_b in
/-- Helper for Lemma 13.13: summing the recurrence on the interval `n = j, …, k` keeps the
terminal value `a (k + 1)` explicit on the left, exactly as in the textbook proof. -/
lemma shifted_scalar_recurrence_interval_sum
    (j k : ℕ) (hjk : j ≤ k) :
    a (k + 1) +
        Finset.sum (Finset.range (k + 1 - j))
          (fun m ↦ (2 / (j + m + 2 * p : ℝ)) * b (j + m)) ≤
      a j +
        (A / 2) *
          Finset.sum (Finset.range (k + 1 - j))
            (fun m ↦ (2 / (j + m + 2 * p : ℝ)) ^ (2 : ℕ)) := by
  let N : ℕ := k + 1 - j
  have hN : j + N = k + 1 := by
    -- The shifted range length is exactly the interval cardinality `k + 1 - j`.
    dsimp [N]
    omega
  -- Sum the source recurrence over the shifted interval length and telescope the `a`-terms.
  have hinterval :
      a (j + N) +
          Finset.sum (Finset.range N)
            (fun m ↦ (2 / (j + m + 2 * p : ℝ)) * b (j + m)) ≤
        a j +
          (A / 2) *
            Finset.sum (Finset.range N)
              (fun m ↦ (2 / (j + m + 2 * p : ℝ)) ^ (2 : ℕ)) := by
    induction N with
    | zero =>
        -- The empty interval contributes no weighted terms.
        simp
    | succ N ih =>
        have hstepN := hstep (j + N)
        rw [shifted_conditional_gradient_stepsize_eq (p := p) hp (j + N)] at hstepN
        have hstepN'' :
            a (j + (N + 1)) ≤
              a (j + N) - (2 / (j + N + 2 * p : ℝ)) * b (j + N) +
                (A / 2) * (2 / (j + N + 2 * p : ℝ)) ^ (2 : ℕ) := by
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hstepN
        have hstepN' :
            a (j + (N + 1)) + (2 / (j + N + 2 * p : ℝ)) * b (j + N) ≤
              a (j + N) + (A / 2) * (2 / (j + N + 2 * p : ℝ)) ^ (2 : ℕ) := by
          linarith
        -- Append the last recurrence step to the already-summed prefix.
        calc
          a (j + (N + 1)) +
              Finset.sum (Finset.range (N + 1))
                (fun m ↦ (2 / (j + m + 2 * p : ℝ)) * b (j + m))
              =
                (a (j + (N + 1)) + (2 / (j + N + 2 * p : ℝ)) * b (j + N)) +
                  Finset.sum (Finset.range N)
                    (fun m ↦ (2 / (j + m + 2 * p : ℝ)) * b (j + m)) := by
                  rw [Finset.sum_range_succ]
                  ring
          _ ≤
                (a (j + N) + (A / 2) * (2 / (j + N + 2 * p : ℝ)) ^ (2 : ℕ)) +
                  Finset.sum (Finset.range N)
                    (fun m ↦ (2 / (j + m + 2 * p : ℝ)) * b (j + m)) := by
                  linarith
          _ ≤
                (a j +
                    (A / 2) *
                      Finset.sum (Finset.range N)
                        (fun m ↦ (2 / (j + m + 2 * p : ℝ)) ^ (2 : ℕ))) +
                  (A / 2) * (2 / (j + N + 2 * p : ℝ)) ^ (2 : ℕ) := by
                  linarith
          _ =
                a j +
                  (A / 2) *
                    Finset.sum (Finset.range (N + 1))
                      (fun m ↦ (2 / (j + m + 2 * p : ℝ)) ^ (2 : ℕ)) := by
                  rw [Finset.sum_range_succ]
                  ring
  simpa [N, hN] using hinterval

omit ha_nonneg hstep ha_le_b in
/-- Helper for Lemma 13.13: the reciprocal-square remainder is controlled by the textbook
telescoping difference `1/(n-1) - 1/n` on the shifted interval. -/
lemma shifted_reciprocal_square_sum_le
    (j k : ℕ) (hjk : j ≤ k) :
    Finset.sum (Finset.range (k + 1 - j))
      (fun m ↦ 1 / (j + m + 2 * p : ℝ) ^ (2 : ℕ)) ≤
      1 / (j + 2 * p - 1 : ℝ) - 1 / (k + 2 * p : ℝ) := by
  have hpointwise :
      ∀ m ∈ Finset.range (k + 1 - j),
        1 / (j + m + 2 * p : ℝ) ^ (2 : ℕ) ≤
          1 / (j + m + 2 * p - 1 : ℝ) - 1 / (j + m + 2 * p : ℝ) := by
    intro m hm
    let n : ℕ := j + m + 2 * p
    have hn_one : 1 ≤ n := by
      dsimp [n]
      omega
    have hn_two : 2 ≤ n := by
      dsimp [n]
      omega
    have hn_pos : 0 < (n : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn_one)
    have hn_sub_pos : 0 < ((n - 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < n - 1 by omega)
    have hmul_le : (((n - 1 : ℕ) : ℝ) * (n : ℝ)) ≤ (n : ℝ) ^ (2 : ℕ) := by
      have hn_sub_le : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast (show n - 1 ≤ n by omega)
      nlinarith
    have hrecip :
        1 / (n : ℝ) ^ (2 : ℕ) ≤ 1 / (((n - 1 : ℕ) : ℝ) * (n : ℝ)) := by
      exact one_div_le_one_div_of_le (mul_pos hn_sub_pos hn_pos) hmul_le
    have hn_cast : (n : ℝ) = (j + m + 2 * p : ℝ) := by
      norm_num [n, Nat.cast_add, Nat.cast_mul]
    have hprev_cast : (((n - 1 : ℕ) : ℝ)) = (j + m + 2 * p - 1 : ℝ) := by
      have hnat : 1 ≤ j + m + 2 * p := by
        omega
      dsimp [n]
      rw [Nat.cast_sub hnat]
      norm_num [Nat.cast_add, Nat.cast_mul]
    have hdelta : (n : ℝ) - (((n - 1 : ℕ) : ℝ)) = 1 := by
      rw [hn_cast, hprev_cast]
      ring
    have hdiff :
        1 / (((n - 1 : ℕ) : ℝ)) - 1 / (n : ℝ) =
          1 / (((n - 1 : ℕ) : ℝ) * (n : ℝ)) := by
      calc
        1 / (((n - 1 : ℕ) : ℝ)) - 1 / (n : ℝ)
            = ((n : ℝ) - (((n - 1 : ℕ) : ℝ))) /
                ((((n - 1 : ℕ) : ℝ) * (n : ℝ))) := by
                  field_simp [hn_pos.ne', hn_sub_pos.ne']
        _ = 1 / (((n - 1 : ℕ) : ℝ) * (n : ℝ)) := by rw [hdelta]
    -- Compare the square remainder to the telescoping difference with the same shifted index.
    calc
      1 / (j + m + 2 * p : ℝ) ^ (2 : ℕ)
          = 1 / (n : ℝ) ^ (2 : ℕ) := by rw [hn_cast]
      _ ≤ 1 / (((n - 1 : ℕ) : ℝ) * (n : ℝ)) := hrecip
      _ = 1 / (((n - 1 : ℕ) : ℝ)) - 1 / (n : ℝ) := hdiff.symm
      _ = 1 / (j + m + 2 * p - 1 : ℝ) - 1 / (j + m + 2 * p : ℝ) := by
            rw [hprev_cast, hn_cast]
  have hsum_le :
      Finset.sum (Finset.range (k + 1 - j))
        (fun m ↦ 1 / (j + m + 2 * p : ℝ) ^ (2 : ℕ)) ≤
        Finset.sum (Finset.range (k + 1 - j))
          (fun m ↦ 1 / (j + m + 2 * p - 1 : ℝ) - 1 / (j + m + 2 * p : ℝ)) := by
    exact Finset.sum_le_sum fun m hm ↦ hpointwise m hm
  have htelescoping :
      Finset.sum (Finset.range (k + 1 - j))
        (fun m ↦ 1 / (j + m + 2 * p - 1 : ℝ) - 1 / (j + m + 2 * p : ℝ)) =
          1 / (j + 2 * p - 1 : ℝ) - 1 / (k + 2 * p : ℝ) := by
    let f : ℕ → ℝ := fun m ↦ 1 / (j + m + 2 * p - 1 : ℝ)
    have htel :
        ∀ N : ℕ,
          Finset.sum (Finset.range N) (fun m ↦ f m - f (m + 1)) = f 0 - f N := by
      intro N
      induction N with
      | zero =>
          simp [f]
      | succ N ih =>
          rw [Finset.sum_range_succ, ih]
          ring
    have hrewrite :
        (fun m : ℕ ↦ 1 / (j + m + 2 * p - 1 : ℝ) - 1 / (j + m + 2 * p : ℝ)) =
          (fun m : ℕ ↦ f m - f (m + 1)) := by
      funext m
      have hsucc_cast : (j + (m + 1) + 2 * p - 1 : ℝ) = j + m + 2 * p := by
        ring
      simp [f, hsucc_cast]
    rw [hrewrite, htel]
    have hsum_cast : (j : ℝ) + ((k + 1 - j : ℕ) : ℝ) = k + 1 := by
      exact_mod_cast (show j + (k + 1 - j) = k + 1 by omega)
    have hstart : f 0 = 1 / (j + 2 * p - 1 : ℝ) := by
      simp [f]
    have hend_den : (j : ℝ) + ((k + 1 - j : ℕ) : ℝ) + 2 * p - 1 = k + 2 * p := by
      nlinarith [hsum_cast]
    have hend_term : f (k + 1 - j) = 1 / (k + 2 * p : ℝ) := by
      dsimp [f]
      rw [hend_den]
    simp [hstart, hend_term]
  calc
    Finset.sum (Finset.range (k + 1 - j))
        (fun m ↦ 1 / (j + m + 2 * p : ℝ) ^ (2 : ℕ))
      ≤
        Finset.sum (Finset.range (k + 1 - j))
          (fun m ↦ 1 / (j + m + 2 * p - 1 : ℝ) - 1 / (j + m + 2 * p : ℝ)) := hsum_le
    _ = 1 / (j + 2 * p - 1 : ℝ) - 1 / (k + 2 * p : ℝ) := htelescoping

/-- Helper for Lemma 13.13: after summing the recurrence and inserting the part `(1)` estimate at
`a j`, the entire weighted tail is controlled by `4M / (j + 2p - 2)`. -/
lemma tail_weighted_sum_le_four_control_div
    (j k : ℕ) (hj : 1 ≤ j) (hjk : j ≤ k) :
    Finset.sum (Finset.range (k + 1 - j))
      (fun m ↦ (2 / (j + m + 2 * p : ℝ)) * b (j + m)) ≤
      (4 * max A ((((p - 1 : ℕ) : ℝ) * a 0))) / (j + 2 * p - 2 : ℝ) := by
  let M : ℝ := max A ((((p - 1 : ℕ) : ℝ) * a 0))
  let G : ℝ :=
    Finset.sum (Finset.range (k + 1 - j))
      (fun m ↦ (2 / (j + m + 2 * p : ℝ)) ^ (2 : ℕ))
  let T : ℝ :=
    Finset.sum (Finset.range (k + 1 - j))
      (fun m ↦ 1 / (j + m + 2 * p : ℝ) ^ (2 : ℕ))
  let U : ℝ := 1 / (j + 2 * p - 1 : ℝ) - 1 / (k + 2 * p : ℝ)
  let d : ℝ := (j + 2 * p - 2 : ℝ)
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    exact scalar_recurrence_control_nonneg (a := a) (A := A) (p := p) ha_nonneg
  have hd_pos : 0 < d := by
    -- The denominator is positive because `j ≥ 1` and `p ≥ 1`.
    dsimp [d]
    have hj_real : (1 : ℝ) ≤ j := by
      exact_mod_cast hj
    have hp_real : (1 : ℝ) ≤ p := by
      exact_mod_cast hp
    nlinarith
  have hsum :
      Finset.sum (Finset.range (k + 1 - j))
        (fun m ↦ (2 / (j + m + 2 * p : ℝ)) * b (j + m)) ≤
          a j + (A / 2) * G := by
    have hinterval0 :=
      shifted_scalar_recurrence_interval_sum
        (a := a) (b := b) (A := A) (p := p) (hp := hp) (hstep := hstep) j k hjk
    have hinterval :
        a (k + 1) +
            Finset.sum (Finset.range (k + 1 - j))
              (fun m ↦ (2 / (j + m + 2 * p : ℝ)) * b (j + m)) ≤
          a j + (A / 2) * G := by
      simpa [G] using hinterval0
    -- Drop the nonnegative terminal term `a (k + 1)` from the exact interval sum.
    have hdrop :
        Finset.sum (Finset.range (k + 1 - j))
          (fun m ↦ (2 / (j + m + 2 * p : ℝ)) * b (j + m)) ≤
            a j + (A / 2) * G := by
      linarith [hinterval, ha_nonneg (k + 1)]
    exact hdrop
  have haj :
      a j ≤ (2 * M) / d := by
    have hcast_d : (((j + 2 * p - 2 : ℕ) : ℝ)) = d := by
      dsimp [d]
      have hnat : 2 ≤ j + 2 * p := by
        omega
      rw [Nat.cast_sub hnat]
      norm_num [Nat.cast_add, Nat.cast_mul]
    have haj' :=
      scalar_recurrence_le_sublinear_bound_of_conditional_gradient_stepsize
        (a := a) (b := b) (A := A) (p := p) hp ha_nonneg hstep ha_le_b (k := j) hj
    simpa [M, hcast_d] using haj'
  have hT_nonneg : 0 ≤ T := by
    dsimp [T]
    refine Finset.sum_nonneg ?_
    intro m hm
    have hden_pos : 0 < (j + m + 2 * p : ℝ) := by
      exact_mod_cast (show 0 < j + m + 2 * p by omega)
    positivity
  have hG_eq :
      (A / 2) * G = 2 * A * T := by
    dsimp [G, T]
    -- Rewrite each quadratic step term into `4 / (j + m + 2p)^2`.
    calc
      (A / 2) *
          Finset.sum (Finset.range (k + 1 - j))
            (fun m ↦ (2 / (j + m + 2 * p : ℝ)) ^ (2 : ℕ))
        =
          (A / 2) *
            Finset.sum (Finset.range (k + 1 - j))
              (fun m ↦ 4 * (1 / (j + m + 2 * p : ℝ) ^ (2 : ℕ))) := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro m hm
            simp [pow_two, div_eq_mul_inv]
            ring
      _ =
          Finset.sum (Finset.range (k + 1 - j))
            (fun m ↦ (A / 2) * (4 * (1 / (j + m + 2 * p : ℝ) ^ (2 : ℕ)))) := by
            rw [Finset.mul_sum]
      _ =
          Finset.sum (Finset.range (k + 1 - j))
            (fun m ↦ 2 * A * (1 / (j + m + 2 * p : ℝ) ^ (2 : ℕ))) := by
            refine Finset.sum_congr rfl ?_
            intro m hm
            ring
      _ = 2 * A *
          Finset.sum (Finset.range (k + 1 - j))
            (fun m ↦ 1 / (j + m + 2 * p : ℝ) ^ (2 : ℕ)) := by
            symm
            rw [Finset.mul_sum]
  have hT_le_U : T ≤ U := by
    dsimp [T, U]
    exact shifted_reciprocal_square_sum_le (p := p) (hp := hp) j k hjk
  by_cases hA_nonneg : 0 ≤ A
  · have hA_le_M : A ≤ M := by
      dsimp [M]
      exact le_max_left _ _
    have hU_nonneg : 0 ≤ U := by
      have hj_pos : 0 < (j + 2 * p - 1 : ℝ) := by
        have hj_real : (1 : ℝ) ≤ j := by
          exact_mod_cast hj
        have hp_real : (1 : ℝ) ≤ p := by
          exact_mod_cast hp
        nlinarith
      have hj_le_k : (j + 2 * p - 1 : ℝ) ≤ (k + 2 * p : ℝ) := by
        have hjk_real : (j : ℝ) ≤ k := by
          exact_mod_cast hjk
        have hp_real : (0 : ℝ) ≤ p := by
          exact_mod_cast (Nat.zero_le p)
        nlinarith
      have hrecip : 1 / (k + 2 * p : ℝ) ≤ 1 / (j + 2 * p - 1 : ℝ) := by
        exact one_div_le_one_div_of_le hj_pos hj_le_k
      dsimp [U]
      exact sub_nonneg.mpr hrecip
    have hU_le_one_div_d : U ≤ 1 / d := by
      have hdrop_last : U ≤ 1 / (j + 2 * p - 1 : ℝ) := by
        have hlast_nonneg : 0 ≤ 1 / (k + 2 * p : ℝ) := by
          positivity
        dsimp [U]
        linarith
      have hd_le : d ≤ (j + 2 * p - 1 : ℝ) := by
        dsimp [d]
        nlinarith
      have hrecip_le : 1 / (j + 2 * p - 1 : ℝ) ≤ 1 / d := by
        exact one_div_le_one_div_of_le hd_pos hd_le
      exact le_trans hdrop_last hrecip_le
    have hremainder :
        (A / 2) * G ≤ 2 * M / d := by
      rw [hG_eq]
      have hAT : A * T ≤ M * T := by
        exact mul_le_mul_of_nonneg_right hA_le_M hT_nonneg
      have hMU : M * T ≤ M * U := by
        exact mul_le_mul_of_nonneg_left hT_le_U hM_nonneg
      have hUd : M * U ≤ M * (1 / d) := by
        exact mul_le_mul_of_nonneg_left hU_le_one_div_d hM_nonneg
      have hdiv : M * (1 / d) = M / d := by
        simp [div_eq_mul_inv]
      have hUd' : 2 * (M * U) ≤ 2 * M / d := by
        have htmp :=
          mul_le_mul_of_nonneg_left hUd (show (0 : ℝ) ≤ 2 by norm_num)
        simpa [hdiv, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using htmp
      calc
        2 * A * T ≤ 2 * (M * T) := by nlinarith
        _ ≤ 2 * (M * U) := by nlinarith [hMU]
        _ ≤ 2 * M / d := hUd'
    -- Insert part `(1)` at `a j` and control the quadratic remainder by the telescoping bound.
    have htarget :
        Finset.sum (Finset.range (k + 1 - j))
          (fun m ↦ (2 / (j + m + 2 * p : ℝ)) * b (j + m)) ≤
            4 * M / d := by
      have hupper : a j + (A / 2) * G ≤ 4 * M / d := by
        calc
          a j + (A / 2) * G ≤ 2 * M / d + 2 * M / d := add_le_add haj hremainder
          _ = 4 * M / d := by ring
      exact le_trans hsum hupper
    dsimp [M, d] at htarget ⊢
    simpa [mul_assoc, mul_left_comm, mul_comm] using htarget
  · have hA_nonpos : A ≤ 0 := le_of_not_ge hA_nonneg
    have hG_nonneg : 0 ≤ G := by
      dsimp [G]
      refine Finset.sum_nonneg ?_
      intro m hm
      positivity
    have hremainder_nonpos : (A / 2) * G ≤ 0 := by
      nlinarith
    have htarget :
        Finset.sum (Finset.range (k + 1 - j))
          (fun m ↦ (2 / (j + m + 2 * p : ℝ)) * b (j + m)) ≤
            4 * M / d := by
      have hupper : a j + (A / 2) * G ≤ 4 * M / d := by
        have hMd_nonneg : 0 ≤ M / d := by
          exact div_nonneg hM_nonneg hd_pos.le
        have hupper₁ : a j + (A / 2) * G ≤ 2 * M / d := by
          calc
            a j + (A / 2) * G ≤ 2 * M / d + 0 := add_le_add haj hremainder_nonpos
            _ = 2 * M / d := by ring
        have hupper₂ : 2 * M / d ≤ 4 * M / d := by
          calc
            2 * M / d = 2 * (M / d) := by ring
            _ ≤ 4 * (M / d) := by
                  exact mul_le_mul_of_nonneg_right (show (2 : ℝ) ≤ 4 by norm_num) hMd_nonneg
            _ = 4 * M / d := by ring
        exact le_trans hupper₁ hupper₂
      exact le_trans hsum hupper
    dsimp [M, d] at htarget ⊢
    simpa [mul_assoc, mul_left_comm, mul_comm] using htarget

omit ha_nonneg hstep ha_le_b in
/-- Helper for Lemma 13.13: over the tail interval `j, …, k`, each shifted stepsize
`2 / (j + m + 2p)` is at least the uniform lower bound `2 / (k + 2p)`, so the total weight is
bounded below by the interval length times that smallest weight. -/
lemma shifted_stepsize_sum_lower
    (j k : ℕ) (hjk : j ≤ k) :
    2 * ((k + 1 - j : ℕ) : ℝ) / (k + 2 * p : ℝ) ≤
      Finset.sum (Finset.range (k + 1 - j)) (fun m ↦ 2 / (j + m + 2 * p : ℝ)) := by
  -- Compare each denominator `j + m + 2p` with the largest one `k + 2p` on the tail interval.
  have hterm :
      ∀ m ∈ Finset.range (k + 1 - j),
        2 / (k + 2 * p : ℝ) ≤ 2 / (j + m + 2 * p : ℝ) := by
    intro m hm
    have hm_lt : m < k + 1 - j := Finset.mem_range.mp hm
    have hindex_le : j + m ≤ k := by
      omega
    have hsmall_pos : 0 < (j + m + 2 * p : ℝ) := by
      positivity
    have hsmall_le_big : (j + m + 2 * p : ℝ) ≤ (k + 2 * p : ℝ) := by
      have hindex_le_real : (j + m : ℝ) ≤ k := by
        exact_mod_cast hindex_le
      nlinarith
    have hrecip :
        (1 / (k + 2 * p : ℝ)) ≤ 1 / (j + m + 2 * p : ℝ) := by
      exact one_div_le_one_div_of_le hsmall_pos hsmall_le_big
    have hscaled :
        2 * (1 / (k + 2 * p : ℝ)) ≤ 2 * (1 / (j + m + 2 * p : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hrecip (by norm_num)
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hscaled
  have hconst_sum :
      Finset.sum (Finset.range (k + 1 - j)) (fun _ ↦ 2 / (k + 2 * p : ℝ)) =
        ((k + 1 - j : ℕ) : ℝ) * (2 / (k + 2 * p : ℝ)) := by
    simp
  -- Sum the pointwise comparison and rewrite the constant sum into the textbook lower bound.
  calc
    2 * ((k + 1 - j : ℕ) : ℝ) / (k + 2 * p : ℝ) =
        ((k + 1 - j : ℕ) : ℝ) * (2 / (k + 2 * p : ℝ)) := by
          ring
    _ = Finset.sum (Finset.range (k + 1 - j)) (fun _ ↦ 2 / (k + 2 * p : ℝ)) := by
          symm
          simp [mul_comm]
    _ ≤ Finset.sum (Finset.range (k + 1 - j)) (fun m ↦ 2 / (j + m + 2 * p : ℝ)) := by
          exact Finset.sum_le_sum fun m hm ↦ hterm m hm

/-- Helper for Lemma 13.13: if the weighted tail is bounded above by the source estimate, then
some index in the interval `j, …, k` already satisfies the corresponding pointwise tail bound. -/
lemma exists_interval_index_le_tail_bound
    (j k : ℕ) (hj : 1 ≤ j) (hjk : j ≤ k) :
    ∃ m ∈ Finset.range (k + 1 - j),
      b (j + m) ≤
        (2 * max A ((((p - 1 : ℕ) : ℝ) * a 0)) * (k + 2 * p : ℝ)) /
          ((((j + 2 * p - 2 : ℕ) : ℝ) * (((k + 1 - j : ℕ) : ℝ)))) := by
  let M : ℝ := max A ((((p - 1 : ℕ) : ℝ) * a 0))
  let N : ℕ := k + 1 - j
  let d : ℝ := (j + 2 * p - 2 : ℝ)
  let B : ℝ := (2 * M * (k + 2 * p : ℝ)) / (d * (N : ℝ))
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    exact scalar_recurrence_control_nonneg (a := a) (A := A) (p := p) ha_nonneg
  have hN_pos_nat : 0 < N := by
    dsimp [N]
    omega
  have hN_pos : 0 < (N : ℝ) := by
    exact_mod_cast hN_pos_nat
  have hd_pos : 0 < d := by
    dsimp [d]
    have hj_real : (1 : ℝ) ≤ j := by
      exact_mod_cast hj
    have hp_real : (1 : ℝ) ≤ p := by
      exact_mod_cast hp
    nlinarith
  have hk_shift_pos : 0 < (k + 2 * p : ℝ) := by
    positivity
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hM_nonneg) hk_shift_pos.le)
      (mul_nonneg hd_pos.le hN_pos.le)
  by_contra hnone
  have htail_lt : ∀ m ∈ Finset.range N, B < b (j + m) := by
    intro m hm
    by_contra hbm
    apply hnone
    refine ⟨m, by simpa [N] using hm, ?_⟩
    have hbm' : b (j + m) ≤ B := le_of_not_gt hbm
    have hcast_d : (((j + 2 * p - 2 : ℕ) : ℝ)) = d := by
      dsimp [d]
      have hnat : 2 ≤ j + 2 * p := by
        omega
      rw [Nat.cast_sub hnat]
      norm_num [Nat.cast_add, Nat.cast_mul]
    dsimp [B, N, M] at hbm'
    simpa [d, hcast_d] using hbm'
  have hweight_pos :
      ∀ m ∈ Finset.range N, 0 < 2 / (j + m + 2 * p : ℝ) := by
    intro m hm
    have hden_pos : 0 < (j + m + 2 * p : ℝ) := by
      exact_mod_cast (show 0 < j + m + 2 * p by omega)
    exact div_pos (by norm_num) hden_pos
  have hscaled_strict :
      Finset.sum (Finset.range N) (fun m ↦ (2 / (j + m + 2 * p : ℝ)) * B) <
        Finset.sum (Finset.range N) (fun m ↦ (2 / (j + m + 2 * p : ℝ)) * b (j + m)) := by
    -- If every tail value is strictly larger than `B`, then so is every weighted term.
    refine Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.2 (Nat.ne_of_gt hN_pos_nat)) ?_
    intro m hm
    exact mul_lt_mul_of_pos_left (htail_lt m hm) (hweight_pos m hm)
  have hscaled_eq :
      Finset.sum (Finset.range N) (fun m ↦ (2 / (j + m + 2 * p : ℝ)) * B) =
        B * Finset.sum (Finset.range N) (fun m ↦ 2 / (j + m + 2 * p : ℝ)) := by
    calc
      Finset.sum (Finset.range N) (fun m ↦ (2 / (j + m + 2 * p : ℝ)) * B) =
          Finset.sum (Finset.range N) (fun m ↦ B * (2 / (j + m + 2 * p : ℝ))) := by
            refine Finset.sum_congr rfl ?_
            intro m hm
            ring
      _ = B * Finset.sum (Finset.range N) (fun m ↦ 2 / (j + m + 2 * p : ℝ)) := by
            rw [Finset.mul_sum]
  have hlower_weighted :
      B * (2 * (N : ℝ) / (k + 2 * p : ℝ)) ≤
        Finset.sum (Finset.range N) (fun m ↦ (2 / (j + m + 2 * p : ℝ)) * B) := by
    rw [hscaled_eq]
    exact mul_le_mul_of_nonneg_left
      (shifted_stepsize_sum_lower (p := p) (hp := hp) j k hjk)
      hB_nonneg
  have hbase_eq : B * (2 * (N : ℝ) / (k + 2 * p : ℝ)) = 4 * M / d := by
    dsimp [B]
    field_simp [hd_pos.ne', hN_pos.ne', hk_shift_pos.ne']
    ring
  have hstrict :
      4 * M / d <
        Finset.sum (Finset.range N) (fun m ↦ (2 / (j + m + 2 * p : ℝ)) * b (j + m)) := by
    calc
      4 * M / d = B * (2 * (N : ℝ) / (k + 2 * p : ℝ)) := by
        symm
        exact hbase_eq
      _ ≤ Finset.sum (Finset.range N) (fun m ↦ (2 / (j + m + 2 * p : ℝ)) * B) := hlower_weighted
      _ < Finset.sum (Finset.range N) (fun m ↦ (2 / (j + m + 2 * p : ℝ)) * b (j + m)) :=
        hscaled_strict
  have hupper :=
    tail_weighted_sum_le_four_control_div
      (a := a) (b := b) (A := A) (p := p) hp ha_nonneg hstep ha_le_b j k hj hjk
  dsimp [M, N, d] at hstrict hupper
  exact (not_lt_of_ge hupper) hstrict

omit ha_nonneg hstep ha_le_b in
/-- Helper for Lemma 13.13: for the textbook choice `j = ⌊k / 2⌋ + 2`, the interval-tail ratio
compresses to the final factor `4 / (k - 2)`. -/
lemma half_tail_ratio_le_four_div
    {k : ℕ} (hk : 3 ≤ k) :
    let j := k / 2 + 2
    ((k + 2 * p : ℕ) : ℝ) /
        ((((j + 2 * p - 2 : ℕ) : ℝ) * (((k + 1 - j : ℕ) : ℝ)))) ≤
      4 / (((k - 2 : ℕ) : ℝ)) := by
  -- Isolate the arithmetic compression after fixing the textbook choice `j = k / 2 + 2`.
  dsimp
  have hk_sub_pos : 0 < ((k - 2 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < k - 2 by omega)
  have hj_factor_pos : 0 < ((k / 2 + 2 + 2 * p - 2 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < k / 2 + 2 + 2 * p - 2 by omega)
  have hlen_pos : 0 < ((k + 1 - (k / 2 + 2) : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < k + 1 - (k / 2 + 2) by omega)
  have hprod_pos :
      0 <
        (((k / 2 + 2 + 2 * p - 2 : ℕ) : ℝ) *
          (((k + 1 - (k / 2 + 2) : ℕ) : ℝ))) := by
    exact mul_pos hj_factor_pos hlen_pos
  have hfirst_nat : k + 2 * p ≤ 2 * (k / 2 + 2 + 2 * p - 2) := by
    omega
  have hsecond_nat : k - 2 ≤ 2 * (k + 1 - (k / 2 + 2)) := by
    omega
  have hfirst :
      ((k + 2 * p : ℕ) : ℝ) ≤ 2 * ((k / 2 + 2 + 2 * p - 2 : ℕ) : ℝ) := by
    exact_mod_cast hfirst_nat
  have hsecond :
      ((k - 2 : ℕ) : ℝ) ≤ 2 * ((k + 1 - (k / 2 + 2) : ℕ) : ℝ) := by
    exact_mod_cast hsecond_nat
  have hcross :
      ((k + 2 * p : ℕ) : ℝ) * ((k - 2 : ℕ) : ℝ) ≤
        4 *
          (((k / 2 + 2 + 2 * p - 2 : ℕ) : ℝ) *
            ((k + 1 - (k / 2 + 2) : ℕ) : ℝ)) := by
    nlinarith
  field_simp [hprod_pos.ne', hk_sub_pos.ne']
  nlinarith [hcross]

include ha_nonneg hstep ha_le_b

/-- Lemma 13.13 (2): for every `k ≥ 3`, some index `n` in the half-tail interval
`{k / 2 + 2, ..., k}` satisfies
`b_n ≤ 8 * max {A, (p - 1) a_0} / (k - 2)`; equivalently, the minimum of `b_n` on that interval
obeys the same bound. -/
theorem exists_half_tail_index_le_sublinear_bound_of_conditional_gradient_stepsize
    {k : ℕ} (hk : 3 ≤ k) :
    ∃ n ∈ Set.Icc (k / 2 + 2) k,
      b n ≤
        (8 * max A ((((p - 1 : ℕ) : ℝ) * a 0))) /
          (((k - 2 : ℕ) : ℝ)) := by
  let j : ℕ := k / 2 + 2
  have hj : 1 ≤ j := by
    dsimp [j]
    omega
  have hjk : j ≤ k := by
    dsimp [j]
    omega
  obtain ⟨m, hm, hbm⟩ :=
    exists_interval_index_le_tail_bound
      (a := a) (b := b) (A := A) (p := p) hp ha_nonneg hstep ha_le_b j k hj hjk
  let n : ℕ := j + m
  have hm_lt : m < k + 1 - j := Finset.mem_range.mp hm
  have hn_mem : n ∈ Set.Icc (k / 2 + 2) k := by
    constructor
    · dsimp [n, j]
      omega
    · dsimp [n, j]
      omega
  let M : ℝ := max A ((((p - 1 : ℕ) : ℝ) * a 0))
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    exact scalar_recurrence_control_nonneg (a := a) (A := A) (p := p) ha_nonneg
  have hratio :
      ((k + 2 * p : ℕ) : ℝ) /
          ((((j + 2 * p - 2 : ℕ) : ℝ) * (((k + 1 - j : ℕ) : ℝ)))) ≤
        4 / (((k - 2 : ℕ) : ℝ)) := by
    dsimp [j]
    simpa using (half_tail_ratio_le_four_div (p := p) (hp := hp) (k := k) hk)
  have hscaled_ratio :
      (2 * M) *
          (((k + 2 * p : ℕ) : ℝ) /
            (((j + 2 * p - 2 : ℕ) : ℝ) * ((k + 1 - j : ℕ) : ℝ))) ≤
        (2 * M) * (4 / ((k - 2 : ℕ) : ℝ)) := by
    exact mul_le_mul_of_nonneg_left hratio (by nlinarith)
  have hbound :
      b n ≤ (8 * M) / (((k - 2 : ℕ) : ℝ)) := by
    have hbm' :
        b n ≤
          (2 * M) *
            (((k + 2 * p : ℕ) : ℝ) /
              (((j + 2 * p - 2 : ℕ) : ℝ) * ((k + 1 - j : ℕ) : ℝ))) := by
      dsimp [n, M] at hbm ⊢
      have hd_pos :
          0 <
            (((j + 2 * p - 2 : ℕ) : ℝ) * ((k + 1 - j : ℕ) : ℝ)) := by
        have hjd_pos : 0 < ((j + 2 * p - 2 : ℕ) : ℝ) := by
          exact_mod_cast (show 0 < j + 2 * p - 2 by omega)
        have hlen_pos : 0 < ((k + 1 - j : ℕ) : ℝ) := by
          exact_mod_cast (show 0 < k + 1 - j by omega)
        exact mul_pos hjd_pos hlen_pos
      have hrewrite :
          (2 * max A ((((p - 1 : ℕ) : ℝ) * a 0)) * (k + 2 * p : ℝ)) /
              (((j + 2 * p - 2 : ℕ) : ℝ) * ((k + 1 - j : ℕ) : ℝ)) =
            (2 * M) *
              (((k + 2 * p : ℕ) : ℝ) /
                (((j + 2 * p - 2 : ℕ) : ℝ) * ((k + 1 - j : ℕ) : ℝ))) := by
        dsimp [M]
        norm_num [Nat.cast_add, Nat.cast_mul]
        ring
      have hbm0 :
          b n ≤
            (2 * max A ((((p - 1 : ℕ) : ℝ) * a 0)) * (k + 2 * p : ℝ)) /
              (((j + 2 * p - 2 : ℕ) : ℝ) * ((k + 1 - j : ℕ) : ℝ)) := by
        simpa [n, Nat.cast_add, Nat.cast_mul, add_assoc, add_left_comm, add_comm] using hbm
      rwa [hrewrite] at hbm0
    have hfinal_rewrite : (2 * M) * (4 / ((k - 2 : ℕ) : ℝ)) = (8 * M) / ((k - 2 : ℕ) : ℝ) := by
      ring
    calc
      b n ≤ (2 * M) * (((k + 2 * p : ℕ) : ℝ) /
          (((j + 2 * p - 2 : ℕ) : ℝ) * ((k + 1 - j : ℕ) : ℝ))) := hbm'
      _ ≤ (2 * M) * (4 / ((k - 2 : ℕ) : ℝ)) := hscaled_ratio
      _ = (8 * M) / ((k - 2 : ℕ) : ℝ) := hfinal_rewrite
  exact ⟨n, hn_mem, by simpa [M] using hbound⟩

end

end

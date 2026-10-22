/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Topology InnerProductSpace

universe u

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]

noncomputable section

/-- The closed linear span of the even-indexed vectors of a sequence in a real Hilbert space. -/
def even_indexed_closed_span (e : ℕ → 𝓗) : Submodule ℝ 𝓗 :=
  (Submodule.span ℝ (Set.range fun n : ℕ ↦ e (2 * n))).topologicalClosure

/-- The rotated even-odd vector `cos (θ n) • e (2n) + sin (θ n) • e (2n + 1)`. -/
def rotated_even_odd_vector (e : ℕ → 𝓗) (θ : ℕ → ℝ) (n : ℕ) : 𝓗 :=
  Real.cos (θ n) • e (2 * n) + Real.sin (θ n) • e (2 * n + 1)

/-- The closed linear span of the rotated even-odd vectors from Example 3.41. -/
def rotated_even_odd_closed_span (e : ℕ → 𝓗) (θ : ℕ → ℝ) : Submodule ℝ 𝓗 :=
  (Submodule.span ℝ (Set.range (rotated_even_odd_vector e θ))).topologicalClosure

-- Proof sketch: the generator `e (2 * n)` belongs to the algebraic span of the even-indexed
-- range, and every point of that span belongs to its topological closure.
/-- Each even-indexed vector of the sequence belongs to its associated closed span. -/
private theorem even_mem_even_indexed_closed_span (e : ℕ → 𝓗) (n : ℕ) :
    e (2 * n) ∈ even_indexed_closed_span e := by
  -- The generator already lies in the algebraic span, hence also in its closure.
  exact (Submodule.span ℝ (Set.range fun n : ℕ ↦ e (2 * n))).le_topologicalClosure
    (Submodule.subset_span (by exact ⟨n, rfl⟩))

-- Proof sketch: the vector `rotated_even_odd_vector e θ n` is one of the generators of the span
-- whose closure defines `rotated_even_odd_closed_span e θ`.
/-- Each rotated even-odd generator belongs to its associated closed span. -/
private theorem rotated_even_odd_vector_mem_rotated_even_odd_closed_span
    (e : ℕ → 𝓗) (θ : ℕ → ℝ) (n : ℕ) :
    rotated_even_odd_vector e θ n ∈ rotated_even_odd_closed_span e θ := by
  -- The rotated vector is one of the generators of the defining span.
  exact (Submodule.span ℝ (Set.range (rotated_even_odd_vector e θ))).le_topologicalClosure
    (Submodule.subset_span (by exact ⟨n, rfl⟩))

-- Proof sketch: `even_indexed_closed_span e` is defined as the topological closure of a
-- submodule, and closures of submodules are closed subsets of the ambient Hilbert space.
/-- Example 3.41 (1): the closed span of the even-indexed vectors is a closed linear subspace. -/
theorem isClosed_even_indexed_closed_span (e : ℕ → 𝓗) :
    IsClosed ((even_indexed_closed_span e : Submodule ℝ 𝓗) : Set 𝓗) := by
  -- This subspace is defined as a topological closure.
  exact Submodule.isClosed_topologicalClosure _

-- Proof sketch: `rotated_even_odd_closed_span e θ` is likewise a topological closure of a
-- submodule, so its underlying subset is closed.
/-- Example 3.41 (2): the closed span of the rotated even-odd vectors is a closed linear
subspace. -/
theorem isClosed_rotated_even_odd_closed_span (e : ℕ → 𝓗) (θ : ℕ → ℝ) :
    IsClosed ((rotated_even_odd_closed_span e θ : Submodule ℝ 𝓗) : Set 𝓗) := by
  -- This subspace is also defined as a topological closure.
  exact Submodule.isClosed_topologicalClosure _

section

variable (e : ℕ → 𝓗)

private lemma even_index_orthonormal (he : Orthonormal ℝ e) :
    Orthonormal ℝ (fun n : ℕ ↦ e (2 * n)) := by
  -- Reindex the original orthonormal family along the injective even map.
  exact Orthonormal.comp he (fun n : ℕ ↦ 2 * n) (by
    intro m n hmn
    exact Nat.eq_of_mul_eq_mul_left (by decide) hmn)

private lemma odd_index_orthonormal (he : Orthonormal ℝ e) :
    Orthonormal ℝ (fun n : ℕ ↦ e (2 * n + 1)) := by
  -- Reindex the original orthonormal family along the injective odd map.
  exact Orthonormal.comp he (fun n : ℕ ↦ 2 * n + 1) (by
    intro m n hmn
    exact Nat.eq_of_mul_eq_mul_left (by decide) (Nat.add_right_cancel hmn))

variable (θ : ℕ → ℝ)

private lemma rotated_even_odd_inner_kronecker (he : Orthonormal ℝ e) (m n : ℕ) :
    ⟪rotated_even_odd_vector e θ m, rotated_even_odd_vector e θ n⟫_ℝ =
      if m = n then 1 else 0 := by
  by_cases hmn : m = n
  · subst n
    -- On the diagonal, the two summands are orthogonal, so the norm square splits.
    have hcross :
        ⟪Real.cos (θ m) • e (2 * m), Real.sin (θ m) • e (2 * m + 1)⟫_ℝ = 0 := by
      have hneq : 2 * m ≠ 2 * m + 1 := by
        omega
      simp [real_inner_smul_left, real_inner_smul_right, he.2 hneq]
    calc
      ⟪rotated_even_odd_vector e θ m, rotated_even_odd_vector e θ m⟫_ℝ
          = ‖rotated_even_odd_vector e θ m‖ ^ 2 := by
              rw [real_inner_self_eq_norm_sq]
      _ = ‖Real.cos (θ m) • e (2 * m)‖ ^ 2 + ‖Real.sin (θ m) • e (2 * m + 1)‖ ^ 2 := by
            simpa [pow_two, rotated_even_odd_vector] using
              norm_add_sq_eq_norm_sq_add_norm_sq_real hcross
      _ = Real.cos (θ m) ^ 2 + Real.sin (θ m) ^ 2 := by
            simp [norm_smul, he.1]
      _ = 1 := by
            have htrig := Real.sin_sq_add_cos_sq (θ m)
            linarith
    simp
  · -- Off the diagonal, every inner-product term vanishes by parity and orthonormality.
    have h_even : 2 * m ≠ 2 * n := by
      omega
    have h_even_odd : 2 * m ≠ 2 * n + 1 := by
      omega
    have h_odd_even : 2 * m + 1 ≠ 2 * n := by
      omega
    have h_odd : 2 * m + 1 ≠ 2 * n + 1 := by
      omega
    rw [rotated_even_odd_vector, rotated_even_odd_vector]
    rw [inner_add_left, inner_add_right, inner_add_right]
    simp [hmn, real_inner_smul_left, real_inner_smul_right, he.2 h_even, he.2 h_even_odd,
      he.2 h_odd_even, he.2 h_odd]

/-- Helper for Example 3.41: the even and odd coordinate functionals agree with the rotated
coordinate functional on each rotated generator. -/
private lemma rotated_coordinate_functional_eq_on_generators (he : Orthonormal ℝ e) (n m : ℕ) :
    (⟪e (2 * n), rotated_even_odd_vector e θ m⟫_ℝ =
        Real.cos (θ n) *
          ⟪rotated_even_odd_vector e θ n, rotated_even_odd_vector e θ m⟫_ℝ) ∧
      (⟪e (2 * n + 1), rotated_even_odd_vector e θ m⟫_ℝ =
        Real.sin (θ n) *
          ⟪rotated_even_odd_vector e θ n, rotated_even_odd_vector e θ m⟫_ℝ) := by
  by_cases hnm : n = m
  · subst m
    -- On the diagonal, both coordinates are read directly from the rotated vector.
    have hneq : 2 * n ≠ 2 * n + 1 := by
      omega
    have hself : ‖rotated_even_odd_vector e θ n‖ ^ 2 = 1 := by
      have hinner :
          ⟪rotated_even_odd_vector e θ n, rotated_even_odd_vector e θ n⟫_ℝ = 1 := by
        simpa using rotated_even_odd_inner_kronecker e θ he n n
      simpa [real_inner_self_eq_norm_sq] using hinner
    constructor
    · calc
        ⟪e (2 * n), rotated_even_odd_vector e θ n⟫_ℝ = Real.cos (θ n) := by
          rw [rotated_even_odd_vector, inner_add_right]
          simp [real_inner_smul_right, he.2 hneq, he.1 (2 * n)]
        _ = Real.cos (θ n) * ‖rotated_even_odd_vector e θ n‖ ^ 2 := by
          rw [hself]
          ring
        _ = Real.cos (θ n) *
            ⟪rotated_even_odd_vector e θ n, rotated_even_odd_vector e θ n⟫_ℝ := by
              rw [real_inner_self_eq_norm_sq]
    · have hneq' : 2 * n + 1 ≠ 2 * n := by
        omega
      calc
        ⟪e (2 * n + 1), rotated_even_odd_vector e θ n⟫_ℝ = Real.sin (θ n) := by
          rw [rotated_even_odd_vector, inner_add_right]
          simp [real_inner_smul_right, he.2 hneq', he.1 (2 * n + 1)]
        _ = Real.sin (θ n) * ‖rotated_even_odd_vector e θ n‖ ^ 2 := by
          rw [hself]
          ring
        _ = Real.sin (θ n) *
            ⟪rotated_even_odd_vector e θ n, rotated_even_odd_vector e θ n⟫_ℝ := by
              rw [real_inner_self_eq_norm_sq]
  · -- Off the diagonal, both coordinates vanish and the rotated Kronecker term is zero.
    have h_even : 2 * n ≠ 2 * m := by
      omega
    have h_even_odd : 2 * n ≠ 2 * m + 1 := by
      omega
    have h_odd_even : 2 * n + 1 ≠ 2 * m := by
      omega
    have h_odd : 2 * n + 1 ≠ 2 * m + 1 := by
      omega
    constructor
    · calc
        ⟪e (2 * n), rotated_even_odd_vector e θ m⟫_ℝ = 0 := by
          rw [rotated_even_odd_vector, inner_add_right]
          simp [real_inner_smul_right, he.2 h_even, he.2 h_even_odd]
        _ = Real.cos (θ n) *
            ⟪rotated_even_odd_vector e θ n, rotated_even_odd_vector e θ m⟫_ℝ := by
              have hrot :
                  ⟪rotated_even_odd_vector e θ n, rotated_even_odd_vector e θ m⟫_ℝ = 0 := by
                simpa [hnm] using rotated_even_odd_inner_kronecker e θ he n m
              rw [hrot]
              ring
    · calc
        ⟪e (2 * n + 1), rotated_even_odd_vector e θ m⟫_ℝ = 0 := by
          rw [rotated_even_odd_vector, inner_add_right]
          simp [real_inner_smul_right, he.2 h_odd_even, he.2 h_odd]
        _ = Real.sin (θ n) *
            ⟪rotated_even_odd_vector e θ n, rotated_even_odd_vector e θ m⟫_ℝ := by
              have hrot :
                  ⟪rotated_even_odd_vector e θ n, rotated_even_odd_vector e θ m⟫_ℝ = 0 := by
                simpa [hnm] using rotated_even_odd_inner_kronecker e θ he n m
              rw [hrot]
              ring

private lemma inner_odd_eq_zero_of_mem_even_indexed_closed_span (he : Orthonormal ℝ e)
    {x : 𝓗} {n : ℕ}
    (hx : x ∈ even_indexed_closed_span e) :
    ⟪e (2 * n + 1), x⟫_ℝ = 0 := by
  -- Compare the odd-coordinate functional with the zero map on the even generators.
  let F : 𝓗 →L[ℝ] ℝ := innerSL ℝ (e (2 * n + 1))
  let G : 𝓗 →L[ℝ] ℝ := 0
  have hEq : Set.EqOn F G (Set.range fun m : ℕ ↦ e (2 * m)) := by
    intro y hy
    rcases hy with ⟨m, rfl⟩
    have hneq : 2 * n + 1 ≠ 2 * m := by
      omega
    simp [F, G, innerSL_apply_apply, he.2 hneq]
  have hEqClosure := ContinuousLinearMap.eqOn_closure_span hEq
  -- The closure-extension step transports the generator identity to the whole closed span.
  simpa [even_indexed_closed_span, F, G, innerSL_apply_apply] using
    hEqClosure (by simpa [even_indexed_closed_span] using hx)

private lemma inner_even_odd_eq_scaled_inner_rotated_of_mem_rotated_even_odd_closed_span
    (he : Orthonormal ℝ e)
    {x : 𝓗} {n : ℕ} (hx : x ∈ rotated_even_odd_closed_span e θ) :
    (⟪e (2 * n), x⟫_ℝ =
        Real.cos (θ n) * ⟪rotated_even_odd_vector e θ n, x⟫_ℝ) ∧
      (⟪e (2 * n + 1), x⟫_ℝ =
        Real.sin (θ n) * ⟪rotated_even_odd_vector e θ n, x⟫_ℝ) := by
  -- Compare the coordinate functionals on the rotated generators before extending by closure.
  let F_even : 𝓗 →L[ℝ] ℝ := innerSL ℝ (e (2 * n))
  let G_even : 𝓗 →L[ℝ] ℝ := Real.cos (θ n) • innerSL ℝ (rotated_even_odd_vector e θ n)
  let F_odd : 𝓗 →L[ℝ] ℝ := innerSL ℝ (e (2 * n + 1))
  let G_odd : 𝓗 →L[ℝ] ℝ := Real.sin (θ n) • innerSL ℝ (rotated_even_odd_vector e θ n)
  have hEqEven : Set.EqOn F_even G_even (Set.range (rotated_even_odd_vector e θ)) := by
    intro y hy
    rcases hy with ⟨m, rfl⟩
    simpa [F_even, G_even, innerSL_apply_apply] using
      (rotated_coordinate_functional_eq_on_generators e θ he n m).1
  have hEqOdd : Set.EqOn F_odd G_odd (Set.range (rotated_even_odd_vector e θ)) := by
    intro y hy
    rcases hy with ⟨m, rfl⟩
    simpa [F_odd, G_odd, innerSL_apply_apply] using
      (rotated_coordinate_functional_eq_on_generators e θ he n m).2
  have hEqEvenClosure := ContinuousLinearMap.eqOn_closure_span hEqEven
  have hEqOddClosure := ContinuousLinearMap.eqOn_closure_span hEqOdd
  -- The same identities now hold on every vector in the closed rotated span.
  constructor
  · simpa [F_even, G_even, innerSL_apply_apply] using
      hEqEvenClosure (by simpa [rotated_even_odd_closed_span] using hx)
  · simpa [F_odd, G_odd, innerSL_apply_apply] using
      hEqOddClosure (by simpa [rotated_even_odd_closed_span] using hx)

private lemma eq_zero_of_mem_rotated_even_odd_closed_span_of_inner_rotated_eq_zero {x : 𝓗}
    (hx : x ∈ rotated_even_odd_closed_span e θ)
    (hinner : ∀ n : ℕ, ⟪rotated_even_odd_vector e θ n, x⟫_ℝ = 0) :
    x = 0 := by
  -- Compare the functional `innerSL ℝ x` with zero on the rotated generators.
  let F : 𝓗 →L[ℝ] ℝ := innerSL ℝ x
  let G : 𝓗 →L[ℝ] ℝ := 0
  have hEq : Set.EqOn F G (Set.range (rotated_even_odd_vector e θ)) := by
    intro y hy
    rcases hy with ⟨n, rfl⟩
    simpa [F, G, innerSL_apply_apply, real_inner_comm] using hinner n
  have hEqClosure := ContinuousLinearMap.eqOn_closure_span hEq
  have hxx : ⟪x, x⟫_ℝ = 0 := by
    have hxx' := hEqClosure (by simpa [rotated_even_odd_closed_span] using hx)
    simpa [rotated_even_odd_closed_span, F, G, innerSL_apply_apply] using hxx'
  exact inner_self_eq_zero.mp hxx

-- Proof sketch: expand an element of the intersection in the orthonormal family `e`; comparison
-- of the coefficients of `e (2 * n)` and `e (2 * n + 1)` gives `b n * sin (θ n) = 0`, and the
-- positivity of `θ n` implies `sin (θ n) > 0`, so all coefficients vanish.
/-- Example 3.41 (3): the even-index closed span and the rotated closed span intersect trivially. -/
theorem disjoint_even_indexed_closed_span_rotated_even_odd_closed_span
    (he : Orthonormal ℝ e)
    (hθ : ∀ n : ℕ, θ n ∈ Set.Ioc (0 : ℝ) (Real.pi / 2)) :
    Disjoint (even_indexed_closed_span e) (rotated_even_odd_closed_span e θ) := by
  -- A vector in the intersection has zero odd coordinates, hence zero rotated coordinates.
  rw [disjoint_iff, eq_bot_iff]
  intro x hx
  have hx_even : x ∈ even_indexed_closed_span e := hx.1
  have hx_rot : x ∈ rotated_even_odd_closed_span e θ := hx.2
  have hrot_zero : ∀ n : ℕ, ⟪rotated_even_odd_vector e θ n, x⟫_ℝ = 0 := by
    intro n
    rcases inner_even_odd_eq_scaled_inner_rotated_of_mem_rotated_even_odd_closed_span
        e θ he hx_rot with ⟨_, hodd⟩
    have hprod : Real.sin (θ n) * ⟪rotated_even_odd_vector e θ n, x⟫_ℝ = 0 := by
      rw [← hodd, inner_odd_eq_zero_of_mem_even_indexed_closed_span e he hx_even]
    have hθn_lt_pi : θ n < Real.pi := by
      linarith [Real.pi_pos, (hθ n).2]
    have hsin_pos : 0 < Real.sin (θ n) := by
      exact Real.sin_pos_of_pos_of_lt_pi (hθ n).1 hθn_lt_pi
    exact (mul_eq_zero.mp hprod).resolve_left (ne_of_gt hsin_pos)
  -- The vanishing of all rotated coordinates forces the vector itself to vanish.
  exact eq_zero_of_mem_rotated_even_odd_closed_span_of_inner_rotated_eq_zero
    e θ hx_rot hrot_zero

end

private lemma not_summable_cos_sq_of_summable_sin_sq (θ : ℕ → ℝ)
    (hθ_square_summable : Summable (fun n : ℕ ↦ Real.sin (θ n) ^ 2)) :
    ¬ Summable (fun n : ℕ ↦ Real.cos (θ n) ^ 2) := by
  intro hcos
  -- Summability forces the sine-square sequence to converge to zero.
  have hsin_tendsto :
      Filter.Tendsto (fun n : ℕ ↦ Real.sin (θ n) ^ 2) Filter.atTop (nhds 0) :=
    hθ_square_summable.tendsto_atTop_zero
  have hsinevent :
      ∀ᶠ n : ℕ in Filter.atTop, Real.sin (θ n) ^ 2 < (1 / 2 : ℝ) := by
    exact hsin_tendsto.eventually_lt_const (by norm_num)
  have hcos_event :
      ∀ᶠ n : ℕ in Filter.atTop, (1 / 2 : ℝ) < Real.cos (θ n) ^ 2 := by
    filter_upwards [hsinevent] with n hsin
    have htrig := Real.sin_sq_add_cos_sq (θ n)
    linarith
  -- A summable real sequence must converge to zero, which conflicts with the uniform lower bound.
  have hcos_tendsto :
      Filter.Tendsto (fun n : ℕ ↦ Real.cos (θ n) ^ 2) Filter.atTop (nhds 0) :=
    hcos.tendsto_atTop_zero
  have hcos_small :
      ∀ᶠ n : ℕ in Filter.atTop, Real.cos (θ n) ^ 2 < (1 / 2 : ℝ) := by
    exact hcos_tendsto.eventually_lt_const (by norm_num)
  rw [Filter.eventually_atTop] at hcos_event hcos_small
  rcases hcos_event with ⟨N₁, hN₁⟩
  rcases hcos_small with ⟨N₂, hN₂⟩
  let N := max N₁ N₂
  have hn_gt : (1 / 2 : ℝ) < Real.cos (θ N) ^ 2 := hN₁ N (le_max_left _ _)
  have hn_lt : Real.cos (θ N) ^ 2 < (1 / 2 : ℝ) := hN₂ N (le_max_right _ _)
  linarith

section

variable [CompleteSpace 𝓗]
variable (e : ℕ → 𝓗) (θ : ℕ → ℝ)
variable (he : Orthonormal ℝ e)
variable (hθ : ∀ n : ℕ, θ n ∈ Set.Ioc (0 : ℝ) (Real.pi / 2))
variable (hθ_square_summable : Summable (fun n : ℕ ↦ Real.sin (θ n) ^ 2))

-- Proof sketch: form `x = ∑ sin (θ n) • e (2 * n + 1)`, which belongs to the Hilbert space by the
-- square-summability hypothesis. Finite partial sums show `x` lies in the closure of the submodule
-- sum, while coefficient comparison in a hypothetical decomposition `x = c + d` forces the even
-- coefficients to be `-cos (θ n)`, contradicting square summability because `θ n ∈ (0, π / 2]`
-- and `sin (θ n) → 0` imply `cos (θ n) → 1`.
/-- Example 3.41 (4): the sum of the even-index closed span and the rotated closed span is not a
closed linear subspace. -/
theorem not_isClosed_sup_even_indexed_closed_span_rotated_even_odd_closed_span
    (he : Orthonormal ℝ e)
    (hθ : ∀ n : ℕ, θ n ∈ Set.Ioc (0 : ℝ) (Real.pi / 2))
    (hθ_square_summable : Summable (fun n : ℕ ↦ Real.sin (θ n) ^ 2)) :
    ¬ IsClosed
      (((even_indexed_closed_span e ⊔ rotated_even_odd_closed_span e θ : Submodule ℝ 𝓗) :
        Set 𝓗)) := by
  -- The witness is the odd series with coefficients `sin (θ n)`.
  let f : ℕ → 𝓗 := fun n ↦ Real.sin (θ n) • e (2 * n + 1)
  let S : Submodule ℝ 𝓗 := even_indexed_closed_span e ⊔ rotated_even_odd_closed_span e θ
  have hodd := odd_index_orthonormal e he
  have hf : Summable f := by
    refine ((hodd.orthogonalFamily).summable_iff_norm_sq_summable
      (fun n ↦ Real.sin (θ n))).2 ?_
    simpa [f, Real.norm_eq_abs] using hθ_square_summable
  let x : 𝓗 := ∑' n, f n
  have hx_odd : ∀ n : ℕ, ⟪e (2 * n + 1), x⟫_ℝ = Real.sin (θ n) := by
    intro n
    have hmap := (hf.hasSum.mapL (innerSL ℝ (e (2 * n + 1)))).tsum_eq
    have hsingle : (∑' b : ℕ, if n = b then Real.sin (θ b) else 0) = Real.sin (θ n) := by
      refine (tsum_eq_single n ?_).trans ?_
      · intro b hb
        have hnb : ¬ n = b := by
          exact fun h ↦ hb h.symm
        simp [hnb]
      · simp
    dsimp [x, f] at hmap
    -- Mapping the convergent series through the odd-coordinate functional recovers the coefficient.
    simpa [hsingle, innerSL_apply_apply, real_inner_smul_right, orthonormal_iff_ite.mp he] using
      hmap.symm
  have hx_even : ∀ n : ℕ, ⟪e (2 * n), x⟫_ℝ = 0 := by
    intro n
    have hmap := (hf.hasSum.mapL (innerSL ℝ (e (2 * n)))).tsum_eq
    have hparity : ∀ b : ℕ, 2 * n ≠ 2 * b + 1 := by
      intro b
      omega
    dsimp [x, f] at hmap
    -- The even coordinates vanish because the series uses only odd basis vectors.
    simpa [innerSL_apply_apply, real_inner_smul_right, orthonormal_iff_ite.mp he, hparity] using
      hmap.symm
  have hpartial_mem :
      ∀ N : ℕ, Finset.sum (Finset.range N) f ∈ S := by
    intro N
    refine Submodule.sum_mem S fun n hn ↦ ?_
    -- Each summand is the sum of one vector in `C` and one vector in `D`.
    refine Submodule.mem_sup.2 ?_
    refine ⟨(-Real.cos (θ n)) • e (2 * n), ?_, rotated_even_odd_vector e θ n, ?_, ?_⟩
    · exact (even_indexed_closed_span e).smul_mem _ (even_mem_even_indexed_closed_span e n)
    · exact rotated_even_odd_vector_mem_rotated_even_odd_closed_span e θ n
    · simp [rotated_even_odd_vector, add_comm, add_left_comm]
  intro hclosed
  have hx_mem_S : x ∈ S := by
    -- Closedness of the sum forces it to contain the limit of its partial sums.
    exact hclosed.mem_of_tendsto hf.hasSum.tendsto_sum_nat
      (Filter.Eventually.of_forall hpartial_mem)
  have hx_mem_sup :
      x ∈ even_indexed_closed_span e ⊔ rotated_even_odd_closed_span e θ := by
    simpa [S] using hx_mem_S
  rcases Submodule.mem_sup.1 hx_mem_sup with ⟨c, hc, d, hd, hxcd⟩
  have hd_coords :
      ∀ n : ℕ,
        (⟪e (2 * n), d⟫_ℝ =
            Real.cos (θ n) * ⟪rotated_even_odd_vector e θ n, d⟫_ℝ) ∧
          (⟪e (2 * n + 1), d⟫_ℝ =
            Real.sin (θ n) * ⟪rotated_even_odd_vector e θ n, d⟫_ℝ) := by
    intro n
    exact inner_even_odd_eq_scaled_inner_rotated_of_mem_rotated_even_odd_closed_span
      e θ he hd
  have hrot_one : ∀ n : ℕ, ⟪rotated_even_odd_vector e θ n, d⟫_ℝ = 1 := by
    intro n
    have hθn_lt_pi : θ n < Real.pi := by
      linarith [Real.pi_pos, (hθ n).2]
    have hsin_pos : 0 < Real.sin (θ n) := by
      exact Real.sin_pos_of_pos_of_lt_pi (hθ n).1 hθn_lt_pi
    have hprod :
        Real.sin (θ n) * ⟪rotated_even_odd_vector e θ n, d⟫_ℝ = Real.sin (θ n) := by
      have hsum_odd :
          ⟪e (2 * n + 1), x⟫_ℝ = ⟪e (2 * n + 1), c⟫_ℝ + ⟪e (2 * n + 1), d⟫_ℝ := by
        rw [← hxcd]
        simp [inner_add_right]
      rw [hx_odd n, inner_odd_eq_zero_of_mem_even_indexed_closed_span e he hc,
        (hd_coords n).2] at hsum_odd
      simpa [add_comm] using hsum_odd.symm
    have hsin_ne : Real.sin (θ n) ≠ 0 := ne_of_gt hsin_pos
    have hprod' :
        ⟪rotated_even_odd_vector e θ n, d⟫_ℝ * Real.sin (θ n) = 1 * Real.sin (θ n) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hprod
    exact mul_right_cancel₀ hsin_ne hprod'
  have hc_even : ∀ n : ℕ, ⟪e (2 * n), c⟫_ℝ = -Real.cos (θ n) := by
    intro n
    have hsum_even :
        ⟪e (2 * n), x⟫_ℝ = ⟪e (2 * n), c⟫_ℝ + ⟪e (2 * n), d⟫_ℝ := by
      rw [← hxcd]
      simp [inner_add_right]
    rw [hx_even n, (hd_coords n).1, hrot_one n] at hsum_even
    linarith
  have hcos_summable : Summable (fun n : ℕ ↦ Real.cos (θ n) ^ 2) := by
    have hsummable_inner :=
      (even_index_orthonormal e he).inner_products_summable c
    convert hsummable_inner using 1
    ext n
    rw [hc_even n]
    simp [Real.norm_eq_abs]
  exact not_summable_cos_sq_of_summable_sin_sq θ hθ_square_summable hcos_summable

end

end

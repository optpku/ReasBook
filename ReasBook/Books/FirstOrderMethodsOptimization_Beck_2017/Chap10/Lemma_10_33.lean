/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_6

-- Declarations for this item will be appended below by the statement pipeline.

section

/- Lemma 10.33 is `source-facing`: it is a scalar estimate for the FISTA momentum recursion.

Domain sampling:
- `fista_momentum_update` from Algorithm 10.13 is the chapter's canonical owner of the recursion
  `t_(k+1) = (1 + √(1 + 4 t_k^2)) / 2`;
- the FISTA momentum sequence `fista_t f g x0 L` from Algorithm 10.6 and the canonical
  `fista_momentum_sequence` reused by `is_mfista_trajectory` in Algorithm 10.11 are downstream
  specializations of this same scalar recurrence.

Since the textbook statement is only about the scalar sequence defined by the recursion, the main
statement is kept at the sequence level and can later be specialized through the existing FISTA
and MFISTA recurrence lemmas without introducing a duplicate momentum-sequence owner.

Layer triage:
- `source-facing`: `fista_momentum_sequence_lower_bound`, the textbook scalar estimate for any
  sequence satisfying the FISTA momentum recursion;
- `core/canonical`: `fista_momentum_update` from Algorithm 10.13;
- `bridge/view`: the standing problem instance together with `fista_t f g x0 L`.

Primitive data:
- the initial value `t 0 = 1`;
- the recurrence `t (k + 1) = fista_momentum_update (t k)`.

Derived API:
- the owner-level scalar estimate `add_one_half_le_fista_momentum_update` from Algorithm 10.13. -/

-- Proof sketch: argue by induction on `k`. The base case is `t 0 = 1 = (0 + 2) / 2`. For the
-- induction step, use `hsucc` together with the owner-level estimate
-- `add_one_half_le_fista_momentum_update` to get `t (k + 1) ≥ t k + 1 / 2`; combining this with
-- the induction hypothesis yields the claimed lower bound at `k + 1`.
/-- Lemma 10.33: if a real sequence starts at `t_0 = 1` and satisfies the FISTA momentum
recursion `t_(k+1) = (1 + √(1 + 4 t_k^2)) / 2`, then `t_k ≥ (k + 2) / 2` for every `k ≥ 0`. -/
theorem fista_momentum_sequence_lower_bound
    {t : ℕ → ℝ}
    (h0 : t 0 = 1)
    (hsucc : ∀ k : ℕ, t (k + 1) = fista_momentum_update (t k))
    (k : ℕ) :
    ((k : ℝ) + 2) / 2 ≤ t k := by
  induction k with
  | zero =>
      -- Reduce the base case to the prescribed initial value `t 0 = 1`.
      simp [h0]
  | succ k hk =>
      -- Rewrite the recurrence as the canonical half-step growth estimate.
      have hstep : t k + 1 / 2 ≤ t (k + 1) := by
        rw [hsucc]
        exact add_one_half_le_fista_momentum_update (t k)
      -- Re-express the target bound so it matches the induction hypothesis plus the half-step.
      calc
        (((k + 1 : ℕ) : ℝ) + 2) / 2 = (((k : ℝ) + 2) + 1) / 2 := by
          norm_num [Nat.cast_add, add_assoc, add_left_comm, add_comm]
        _ = ((k : ℝ) + 2) / 2 + 1 / 2 := by
          ring
        _ ≤ t k + 1 / 2 := by
          linarith
        _ ≤ t (k + 1) := hstep

end

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
variable {f : E → ℝ} {g : E → EReal}
variable [IsProperExtendedRealFunction g] [Fact (LowerSemicontinuous g)]
  [Fact (is_convex_function g)]

/-- The FISTA momentum sequence attached to a fast proximal-gradient problem satisfies the lower
bound from Lemma 10.33. This is an owner-level statement for the canonical sequence `fista_t`. -/
theorem fista_t_lower_bound
    (x0 : E) (L : ℕ → PosReal) (k : ℕ) :
    ((k : ℝ) + 2) / 2 ≤ fista_t f g x0 L k := by
  -- Specialize the generic scalar recurrence bound to the canonical FISTA momentum sequence.
  simpa using
    fista_momentum_sequence_lower_bound
      (t := fun n ↦ fista_t f g x0 L n)
      (h0 := fista_t_zero f g x0 L)
      (hsucc := fun n ↦ fista_t_succ f g x0 L n)
      k

end

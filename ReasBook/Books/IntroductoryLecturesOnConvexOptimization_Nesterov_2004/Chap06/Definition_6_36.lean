/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_35

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

/- This item lies in the parity-switched scalar-indexing domain.

Sampled owner-style declarations:
- project `smoothness_parameters` in `Definition_6_34`, a nearby Chapter 6 pair-valued scalar
  owner;
- mathlib's parity predicates `Even` and `Odd`, which supply the canonical case split on `k`;
- project `alpha_succ_eq_one_sub_tau_mul_pred_of_alternating_scalar_updates` in `Lemma_6_2_4`,
  which consumes the parity-switched coordinates through separate first/second projection lemmas;
- project `tau_square_bound_iff_alpha_three_term_inequality` in `Theorem_6_5`, which uses the
  predecessor/current/successor index surface attached to the same `α`-sequence.

Best owner abstraction:
- source-facing: the ordered pair `(λ₁,k, λ₂,k)` attached to a sequence `α_k`;
- core/canonical: a pair-valued sequence `switching_parameters α : ℕ → M × M`;
- bridge/view: the even/odd formulas for the first and second coordinates, together with the
  canonical predecessor/current/successor indices into the source `α`-sequence.

Primitive data:
- the source sequence `α : Set.Ici (-1 : ℤ) → M`;
- the parity of the step index `k`.

Derived API:
- the canonical indices `k - 1`, `k`, and `k + 1` as elements of `Set.Ici (-1 : ℤ)`;
- the even/odd coordinate formulas recovering `λ₁,k` and `λ₂,k`.

This item introduces new source-facing sequence data rather than recalling an existing canonical
owner, so the correct Lean surface is a pair-valued definition with coordinate theorems, not a
recall block or an auxiliary wrapper package.
-/

variable {M : Type u}

-- Proof sketch: the integer index `(k : ℤ)` is always at least `-1` because `k ≥ 0`.
/-- The current index `k` lies in the source domain `\{n : ℤ | -1 ≤ n\}`. -/
theorem switching_parameters_curr_index_mem (k : ℕ) :
    (-1 : ℤ) ≤ (k : ℤ) := by
  -- Reduce to Presburger arithmetic on the integer coercion of `k`.
  omega

/-- The source sequence index corresponding to `α_k`. -/
def switching_parameters_curr_index (k : ℕ) : Set.Ici (-1 : ℤ) :=
  ⟨(k : ℤ), switching_parameters_curr_index_mem k⟩

-- Proof sketch: rewrite `-1 ≤ (k : ℤ) - 1` as `0 ≤ (k : ℤ)`.
/-- The predecessor index `k - 1` also lies in the source domain `\{n : ℤ | -1 ≤ n\}`. -/
theorem switching_parameters_pred_index_mem (k : ℕ) :
    (-1 : ℤ) ≤ (k : ℤ) - 1 := by
  -- Normalize the predecessor inequality to the same arithmetic fact about `k`.
  omega

/-- The source sequence index corresponding to `α_{k-1}`. -/
def switching_parameters_pred_index (k : ℕ) : Set.Ici (-1 : ℤ) :=
  ⟨(k : ℤ) - 1, switching_parameters_pred_index_mem k⟩

-- Proof sketch: since `(k : ℤ) + 1 ≥ 1`, it is certainly at least `-1`.
/-- The successor index `k + 1` lies in the source domain `\{n : ℤ | -1 ≤ n\}`. -/
theorem switching_parameters_succ_index_mem (k : ℕ) :
    (-1 : ℤ) ≤ (k : ℤ) + 1 := by
  -- The successor inequality is again a direct Presburger arithmetic consequence.
  omega

/-- The source sequence index corresponding to `α_{k+1}`. -/
def switching_parameters_succ_index (k : ℕ) : Set.Ici (-1 : ℤ) :=
  ⟨(k : ℤ) + 1, switching_parameters_succ_index_mem k⟩

/-- Definition 6.36 [Chapter6_2.json:79]: for a sequence `α_k` indexed by integers `k ≥ -1`,
`switching_parameters α k = (λ₁,k, λ₂,k)`, where for even `k` one has
`λ₁,k = α_{k-1}` and `λ₂,k = α_k`, while for odd `k` one has
`λ₁,k = α_k` and `λ₂,k = α_{k-1}`. -/
def switching_parameters (α : Set.Ici (-1 : ℤ) → M) (k : ℕ) : M × M :=
  if Even k then
    (α (switching_parameters_pred_index k), α (switching_parameters_curr_index k))
  else
    (α (switching_parameters_curr_index k), α (switching_parameters_pred_index k))

-- Proof sketch: unfold `switching_parameters` and simplify the parity split using `hk`.
/-- For an even step, the switching-parameter pair is `(α_{k-1}, α_k)`. -/
theorem switching_parameters_of_even (α : Set.Ici (-1 : ℤ) → M) {k : ℕ} (hk : Even k) :
    switching_parameters α k =
      (α (switching_parameters_pred_index k), α (switching_parameters_curr_index k)) := by
  -- Normalize the parity split using the supplied evenness witness.
  simp [switching_parameters, hk]

-- Proof sketch: unfold `switching_parameters` and simplify the parity split using `hk`.
/-- For an odd step, the switching-parameter pair is `(α_k, α_{k-1})`. -/
theorem switching_parameters_of_odd (α : Set.Ici (-1 : ℤ) → M) {k : ℕ} (hk : Odd k) :
    switching_parameters α k =
      (α (switching_parameters_curr_index k), α (switching_parameters_pred_index k)) := by
  -- Convert oddness into the negation of the even branch, then simplify the `if`.
  have hk_not_even : ¬ Even k := Nat.not_even_iff_odd.2 hk
  simp [switching_parameters, hk_not_even]

-- Proof sketch: take the first projection of `switching_parameters_of_even`.
/-- For even `k`, the first switching parameter equals `α_{k-1}`. -/
theorem first_switching_parameter_of_even (α : Set.Ici (-1 : ℤ) → M) {k : ℕ} (hk : Even k) :
    (switching_parameters α k).1 = α (switching_parameters_pred_index k) := by
  -- Project the even-branch pair identity to its first coordinate.
  simpa using congrArg Prod.fst (switching_parameters_of_even α hk)

-- Proof sketch: take the second projection of `switching_parameters_of_even`.
/-- For even `k`, the second switching parameter equals `α_k`. -/
theorem second_switching_parameter_of_even (α : Set.Ici (-1 : ℤ) → M) {k : ℕ} (hk : Even k) :
    (switching_parameters α k).2 = α (switching_parameters_curr_index k) := by
  -- Project the even-branch pair identity to its second coordinate.
  simpa using congrArg Prod.snd (switching_parameters_of_even α hk)

-- Proof sketch: take the first projection of `switching_parameters_of_odd`.
/-- For odd `k`, the first switching parameter equals `α_k`. -/
theorem first_switching_parameter_of_odd (α : Set.Ici (-1 : ℤ) → M) {k : ℕ} (hk : Odd k) :
    (switching_parameters α k).1 = α (switching_parameters_curr_index k) := by
  -- Project the odd-branch pair identity to its first coordinate.
  simpa using congrArg Prod.fst (switching_parameters_of_odd α hk)

-- Proof sketch: take the second projection of `switching_parameters_of_odd`.
/-- For odd `k`, the second switching parameter equals `α_{k-1}`. -/
theorem second_switching_parameter_of_odd (α : Set.Ici (-1 : ℤ) → M) {k : ℕ} (hk : Odd k) :
    (switching_parameters α k).2 = α (switching_parameters_pred_index k) := by
  -- Project the odd-branch pair identity to its second coordinate.
  simpa using congrArg Prod.snd (switching_parameters_of_odd α hk)

end

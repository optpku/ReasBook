/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Lemma_10_61
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_4

local notation "Λ[" a "]" => primalCounterparts a

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Definition 10.64 is `source-facing`: it identifies the chapter owner
`Λ[a] : Set E` with the subdifferential of the continuous-dual norm at the
dual vector `a`. Domain sampling for the surrounding convex-analysis API gives:
- `Λ[·]` from Lemma 10.61 as the source-facing owner object;
- `subdifferentialAt` from Theorem 3.4 as the `core/canonical` subdifferential owner;
- `NormedSpace.inclusionInDoubleDual ℝ E` as the canonical `bridge/view` from primal vectors to the
  bidual-valued strong-dual subgradients of the continuous-dual norm.

The primitive data are only the dual vector `a`. The primal set `Λ[a]` should therefore remain the
public source-facing object, while the strong-dual subdifferential is used through this canonical
bridge instead of replacing `Λ[a]` by a second owner living on the bidual. -/

-- Proof sketch: unfold `Λ[a]` using Lemma 10.61. For `x : E`, membership in the transported
-- strong-dual subdifferential says that the bidual evaluation functional
-- `NormedSpace.inclusionInDoubleDual ℝ E x`, i.e. `b ↦ b x`, satisfies the subgradient inequality
-- for `h(a) = ‖a‖` at `a`. Evaluating that inequality at `0` yields `‖x‖ ≤ 1`, while
-- evaluating it along positive multiples of `a` yields `a x = ‖a‖`; conversely these two
-- conditions imply the subgradient inequality by the dual-pairing bound
-- `b x ≤ ‖b‖ ‖x‖ ≤ ‖b‖`.
/-- Helper for Definition 10.64: membership of the bidual evaluation functional in the norm
subdifferential is exactly the pointwise subgradient inequality `‖b‖ ≥ ‖a‖ + (b - a)(x)`. -/
lemma mem_subdifferentialAt_norm_iff_eval_subgradient_inequality
    (a : StrongDual ℝ E) {x : E} :
    NormedSpace.inclusionInDoubleDual ℝ E x ∈
        subdifferentialAt (fun b : StrongDual ℝ E ↦ ‖b‖) a ↔
      ∀ b : StrongDual ℝ E, ‖b‖ ≥ ‖a‖ + ((b - a) x : ℝ) := by
  -- Rewrite the real-valued owner predicate into the usual subgradient inequality.
  rw [subdifferentialAt, mem_strongDualSubdifferential, mem_subdifferential,
    is_subgradient_at_coe_iff]
  -- The bidual inclusion acts by evaluation on the original dual space.
  simp [NormedSpace.dual_def]

/-- Helper for Definition 10.64: a primal counterpart satisfies the norm subgradient inequality
after identifying the bidual evaluation functional with `b ↦ b x`. -/
lemma mem_primalCounterparts_implies_eval_subgradient_inequality
    (a : StrongDual ℝ E) {x : E} (hx : x ∈ Λ[a]) :
    ∀ b : StrongDual ℝ E, ‖b‖ ≥ ‖a‖ + ((b - a) x : ℝ) := by
  rcases hx with ⟨hx_norm, hx_apply⟩
  intro b
  -- Control `b x` by the operator norm on the closed unit ball.
  have hbx : b x ≤ ‖b‖ := by
    have hunit : ‖b x‖ ≤ ‖b‖ := b.unit_le_opNorm x hx_norm
    calc
      b x ≤ ‖b x‖ := le_abs_self (b x)
      _ ≤ ‖b‖ := by simpa [Real.norm_eq_abs] using hunit
  -- The source equality `a x = ‖a‖` turns the subgradient inequality into the same bound.
  have hineq' : ‖a‖ + ((b - a) x : ℝ) ≤ ‖b‖ := by
    calc
      ‖a‖ + ((b - a) x : ℝ) = b x := by
        rw [ContinuousLinearMap.sub_apply, hx_apply]
        ring
      _ ≤ ‖b‖ := hbx
  exact hineq'

/-- Helper for Definition 10.64: the pointwise norm subgradient inequality forces the defining
equalities `a x = ‖a‖` and `‖x‖ ≤ 1` of the source counterpart set `Λ[a]`. -/
lemma apply_eq_norm_and_norm_le_one_of_eval_subgradient_inequality
    (a : StrongDual ℝ E) {x : E}
    (hineq : ∀ b : StrongDual ℝ E, ‖b‖ ≥ ‖a‖ + ((b - a) x : ℝ)) :
    a x = ‖a‖ ∧ ‖x‖ ≤ 1 := by
  -- Probe the inequality at `0` and `2 • a` to recover the norming equality.
  have hzero' : ‖a‖ - a x ≤ 0 := by
    simpa using hineq 0
  have h_ax_ge : ‖a‖ ≤ a x := sub_nonpos.mp hzero'
  have htwo' : 2 * ‖a‖ ≥ ‖a‖ + a x := by
    calc
      2 * ‖a‖ = ‖(2 : ℝ) • a‖ := by rw [norm_smul, Real.norm_ofNat]
      _ ≥ ‖a‖ + ((((2 : ℝ) • a) - a) x : ℝ) := hineq ((2 : ℝ) • a)
      _ = ‖a‖ + a x := by
        rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply]
        rw [smul_eq_mul, sub_eq_add_neg]
        ring
  have h_ax_le : a x ≤ ‖a‖ := by
    linarith
  have hax : a x = ‖a‖ := le_antisymm h_ax_le h_ax_ge
  -- Substitute the equality back to obtain the dual bound `|b x| ≤ ‖b‖` for every `b`.
  have h_eval_le : ∀ b : StrongDual ℝ E, b x ≤ ‖b‖ := by
    intro b
    have hb : ‖a‖ + ((b - a) x : ℝ) ≤ ‖b‖ := hineq b
    calc
      b x = ‖a‖ + ((b - a) x : ℝ) := by
        rw [ContinuousLinearMap.sub_apply, hax]
        ring
      _ ≤ ‖b‖ := hb
  have hdual_bound : ∀ b : StrongDual ℝ E, ‖b x‖ ≤ 1 * ‖b‖ := by
    intro b
    have hneg_eval : -(b x) ≤ ‖b‖ := by
      simpa using h_eval_le (-b)
    have habs : |b x| ≤ ‖b‖ := by
      refine abs_le.2 ?_
      constructor
      · linarith
      · exact h_eval_le b
    simpa [Real.norm_eq_abs] using habs
  -- The canonical double-dual estimate converts the functional bound into `‖x‖ ≤ 1`.
  have hone_nonneg : (0 : ℝ) ≤ 1 := by
    positivity
  have hnorm : ‖x‖ ≤ 1 :=
    NormedSpace.norm_le_dual_bound (𝕜 := ℝ) x (M := 1) hone_nonneg hdual_bound
  exact ⟨hax, hnorm⟩

/-- Definition 10.64, pointwise bridge form: a primal vector `x` is a source counterpart
`x ∈ Λ[a]` exactly when its canonical bidual image belongs to the norm subdifferential at `a`. -/
@[simp] theorem mem_primalCounterparts_iff_mem_subdifferentialAt_norm
    (a : StrongDual ℝ E) {x : E} :
    x ∈ Λ[a] ↔
      NormedSpace.inclusionInDoubleDual ℝ E x ∈
        subdifferentialAt (fun b : StrongDual ℝ E ↦ ‖b‖) a := by
  constructor
  · intro hx
    -- Translate the source-facing counterpart conditions into the canonical subgradient inequality.
    exact (mem_subdifferentialAt_norm_iff_eval_subgradient_inequality a).2
      (mem_primalCounterparts_implies_eval_subgradient_inequality a hx)
  · intro hx
    -- Convert the subgradient inequality back into the two defining clauses of `Λ[a]`.
    have hineq :
        ∀ b : StrongDual ℝ E, ‖b‖ ≥ ‖a‖ + ((b - a) x : ℝ) :=
      (mem_subdifferentialAt_norm_iff_eval_subgradient_inequality a).1 hx
    rcases apply_eq_norm_and_norm_le_one_of_eval_subgradient_inequality a hineq with
      ⟨hax, hnorm⟩
    exact ⟨hnorm, hax⟩

/-- Definition 10.64: the source set `Λ_a` is the subdifferential of the continuous-dual norm
`h(a) = ‖a‖`, transported from the bidual-valued owner `subdifferentialAt` back to the primal
space by the canonical map
`NormedSpace.inclusionInDoubleDual ℝ E`. -/
theorem primalCounterparts_eq_preimage_subdifferentialAt_norm
    (a : StrongDual ℝ E) :
    Λ[a] =
      (NormedSpace.inclusionInDoubleDual ℝ E) ⁻¹'
        subdifferentialAt (fun b : StrongDual ℝ E ↦ ‖b‖) a := by
  ext x
  simp [mem_primalCounterparts_iff_mem_subdifferentialAt_norm]

end

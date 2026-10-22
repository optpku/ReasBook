/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Tactic.Recall
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Proposition_12_9
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Proposition_12_27

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

section MoreauEnvelope

variable {H : Type u} [NormedAddCommGroup H]

/- Source/core/bridge triage:
- `source-facing`: Proposition 12.33 states these clauses in Moreau-envelope notation.
- `core/canonical`: the owner abstraction is `normPowerEnvelope`.
- `bridge/view`: `{}^[γ] f` is the canonical `p = 2` specialization from Proposition 12.9. -/

-- Proof sketch: specialize Proposition 12.9(ii) at `p = 2`, then rewrite the resulting
-- `normPowerEnvelope` statement through `normPowerEnvelope_two_eq_moreauEnvelope`.
/-- Proposition 12.33 (1): for `f : H → ]-∞,+∞]` and `x ∈ H`, the Moreau-envelope net
`γ ↦ ({}^[γ] f) x` is decreasing on `ℝ_{++}`. -/
theorem antitone_moreauEnvelope_along_parameter
    (f : H → Set.Ioi (⊥ : EReal)) (x : H) :
    Antitone (fun γ : PosReal ↦ ({}^[γ] f) x) := sorry

-- Proof sketch: specialize Proposition 12.9(iv) at `p = 2`, then rewrite the envelope by
-- `normPowerEnvelope_two_eq_moreauEnvelope`.
/-- Proposition 12.33 (3): clause (i), the Moreau-envelope values `({}^[γ] f) x` converge
downward to `inf f(H)` as `γ → +∞`. -/
theorem tendsto_moreauEnvelope_atTop_inf
    (f : H → Set.Ioi (⊥ : EReal)) (x : H) :
    Filter.Tendsto (fun γ : PosReal ↦ ({}^[γ] f) x) Filter.atTop
      (nhds (sInf (Set.range f.asEReal))) := sorry

variable [NormedSpace ℝ H]

-- Proof sketch: use the monotonicity from Proposition 12.9(ii), identify the supremum of the
-- increasing net with its right-limit at `0`, and then bound it above and below by `f x`.
/-- Proposition 12.33 (5): clause (ii), the Moreau-envelope values `({}^[γ] f) x` converge upward
to `f x` as `γ ↓ 0` through `ℝ_{++}`. -/
theorem tendsto_moreauEnvelope_atZeroRight_of_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (x : H) :
    Filter.Tendsto (fun γ : PosReal ↦ ({}^[γ] f) x)
      (Filter.comap ((↑) : PosReal → ℝ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)))
      (nhds (f x : EReal)) := sorry

end MoreauEnvelope

section ScaledProximityOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: this is the monotonicity of proximal values from Proposition 12.27, rewritten
-- using the scaled proximity operator `Prox_{γ f}`.
/- Proposition 12.33 (2): for `f ∈ Γ₀(H)` and `x ∈ H`, the proximal-value net
`γ ↦ f (Prox_{γ f} x)` is decreasing on `ℝ_{++}`. This is exactly the canonical owner theorem from
Proposition 12.27. -/
recall antitone_proxValue_along_parameter_of_mem_gammaZero

-- Proof sketch: combine the decomposition
-- `({}^[γ] f) x = f (Prox_{γ f} x) + ‖x - Prox_{γ f} x‖² / (2γ)` with the preceding limit for the
-- Moreau envelope and the obvious lower bound by `inf f(H)`.
/-- Proposition 12.33 (4): clause (i), the proximal values `f (Prox_{γ f} x)` converge downward to
`inf f(H)` as `γ → +∞`. -/
theorem tendsto_scaledProxValue_atTop_inf_of_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (x : H) :
    Filter.Tendsto
      (fun γ : PosReal ↦ f.asEReal (Prox[γ, f, hf] x))
      Filter.atTop
      (nhds (sInf (Set.range f.asEReal))) := sorry

-- Proof sketch: once `x` lies in the effective domain, the proximal points stay in a bounded
-- sublevel set of the coercive perturbation `f + (1 / 2) ‖x - ·‖²`; lower semicontinuity then
-- identifies the right-limit with `f x`.
/-- Proposition 12.33 (6): clause (iii), if `x ∈ dom f`, then the proximal values
`f (Prox_{γ f} x)` converge upward to `f(x)` as `γ ↓ 0` through `ℝ_{++}`. -/
theorem tendsto_scaledProxValue_atZeroRight_of_mem_effectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (x : H) (hx : x ∈ effectiveDomain f) :
    Filter.Tendsto
      (fun γ : PosReal ↦ f.asEReal (Prox[γ, f, hf] x))
      (Filter.comap ((↑) : PosReal → ℝ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)))
      (nhds (f.asEReal x)) := sorry

-- Proof sketch: use the affine minorant from Theorem 9.20 together with the Moreau-envelope
-- decomposition to bound `γ⁻¹ ‖x - Prox_{γ f} x‖²` by a constant multiple of `γ`, then pass to
-- the limit as `γ ↓ 0`.
/-- Proposition 12.33 (7): clause (iii), if `x ∈ dom f`, then the scaled residual energy
`γ⁻¹ ‖x - Prox_{γ f} x‖²` tends to `0` as `γ ↓ 0` through `ℝ_{++}`. -/
theorem tendsto_inv_mul_sqDist_scaledProximityOperator_atZeroRight_of_mem_effectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (x : H) (hx : x ∈ effectiveDomain f) :
    Filter.Tendsto
      (fun γ : PosReal ↦
        ((γ : ℝ)⁻¹ * ‖x - Prox[γ, f, hf] x‖ ^ 2))
      (Filter.comap ((↑) : PosReal → ℝ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)))
      (nhds (0 : ℝ)) := sorry

end ScaledProximityOperator

end ERealFunction

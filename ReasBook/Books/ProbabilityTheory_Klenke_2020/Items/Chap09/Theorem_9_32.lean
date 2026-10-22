/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Probability.Notation
import Mathlib.Probability.Martingale.Basic

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory

universe u v

variable {ι : Type u} {Ω : Type v} [Preorder ι]
variable {m0 : MeasurableSpace Ω}
variable {ℱ : Filtration ι m0} {μ : Measure Ω}

section General

variable {X Y : ι → Ω → ℝ}

-- Proof sketch: combine `Supermartingale.neg` and `Submartingale.neg`, noting that negating twice
-- returns the original process.
/-- Helper for Theorem 9.32: part (1) shows that a process is a supermartingale exactly when its
pointwise negative is a submartingale. -/
theorem supermartingale_iff_neg_submartingale :
    Supermartingale X ℱ μ ↔ Submartingale (-X) ℱ μ := by
  constructor
  · intro hX
    -- Negation converts the supermartingale inequality into the submartingale inequality.
    simpa using hX.neg
  · intro hX
    -- Negating back recovers the original process.
    simpa using hX.neg

-- Proof sketch: scale each martingale by `a` and `b` using `Martingale.smul`, then add the two
-- resulting martingales with `Martingale.add`.
/-- Helper for Theorem 9.32: part (2) shows that real linear combinations of martingales are again
martingales. -/
theorem martingale_linear_combination (hX : Martingale X ℱ μ) (hY : Martingale Y ℱ μ)
    (a b : ℝ) :
    Martingale (a • X + b • Y) ℱ μ := by
  -- Scale each martingale and then add the two resulting martingales.
  exact (hX.smul a).add (hY.smul b)

-- Proof sketch: apply `Supermartingale.smul_nonneg` to `X` and `Y`, then use
-- `Supermartingale.add` to combine the two nonnegative scalar multiples.
/-- Helper for Theorem 9.32: part (3) shows that nonnegative real linear combinations of
supermartingales are again supermartingales. -/
theorem supermartingale_nonneg_linear_combination (hX : Supermartingale X ℱ μ)
    (hY : Supermartingale Y ℱ μ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Supermartingale (a • X + b • Y) ℱ μ := by
  -- Nonnegative scalar multiples preserve the supermartingale property, and sums do as well.
  exact (hX.smul_nonneg ha).add (hY.smul_nonneg hb)

-- Proof sketch: negate both supermartingales to obtain submartingales, use
-- `Submartingale.sup` on the pointwise maxima, and negate back to identify the pointwise minimum.
/-- Helper for Theorem 9.32: part (4) shows that the pointwise minimum of two supermartingales is
again a supermartingale. -/
theorem supermartingale_inf (hX : Supermartingale X ℱ μ) (hY : Supermartingale Y ℱ μ) :
    Supermartingale (X ⊓ Y) ℱ μ := by
  -- Pass to the negatives, take the pointwise supremum there, and negate back.
  have hsup : Submartingale ((-X) ⊔ (-Y)) ℱ μ := hX.neg.sup hY.neg
  simpa [neg_sup] using hsup.neg

end General

variable {𝒢 : Filtration ℕ m0}

section Nat

variable {X : ℕ → Ω → ℝ}

/-- Helper for Theorem 9.32: if a discrete-time supermartingale does not lose expectation by time
`T`, then the terminal conditional expectation at any earlier time `r ≤ T` agrees almost surely
with the process itself at time `r`. -/
lemma condExp_terminal_ae_eq_self_of_expectation_ge [SigmaFiniteFiltration μ 𝒢]
    (hX : Supermartingale X 𝒢 μ) {T r : ℕ} (hrT : r ≤ T) (hEX : μ[X T] ≥ μ[X 0]) :
    μ[X T | 𝒢 r] =ᵐ[μ] X r := by
  -- The supermartingale property gives the pointwise inequality between the two random variables.
  have hle : μ[X T | 𝒢 r] ≤ᵐ[μ] X r := hX.condExp_ae_le hrT
  -- Their expectations must coincide because the supermartingale expectations can only decrease.
  have hTr_le : μ[X T] ≤ μ[X r] := by
    simpa [setIntegral_univ] using hX.setIntegral_le hrT MeasurableSet.univ
  have hr0_le : μ[X r] ≤ μ[X 0] := by
    simpa [setIntegral_univ] using hX.setIntegral_le (Nat.zero_le r) MeasurableSet.univ
  have hTr : μ[X T] = μ[X r] := le_antisymm hTr_le (hr0_le.trans hEX)
  have hIntegralEq : ∫ ω, μ[X T | 𝒢 r] ω ∂μ = ∫ ω, X r ω ∂μ := by
    calc
      ∫ ω, μ[X T | 𝒢 r] ω ∂μ = μ[X T] := by
        simpa using integral_condExp (𝒢.le r) (μ := μ) (f := X T)
      _ = μ[X r] := hTr
      _ = ∫ ω, X r ω ∂μ := by
        rfl
  -- Equality of expectations upgrades the a.e. inequality to a.e. equality.
  exact (integral_eq_iff_of_ae_le integrable_condExp (hX.integrable r) hle).mp hIntegralEq

-- Proof sketch: set `Y s = μ[X T | 𝒢 s]`; this is a martingale by `martingale_condExp`, it lies
-- below `X` by the supermartingale property, and the expectation hypothesis forces equality at
-- every time `s ≤ T`.
/-- Helper for Theorem 9.32: part (5) upgrades the supermartingale conditional-expectation
inequality to an equality on a finite horizon once the terminal expectation matches the initial
one. -/
theorem supermartingale_condExp_ae_eq_of_expectation_ge [SigmaFiniteFiltration μ 𝒢]
    (hX : Supermartingale X 𝒢 μ) {T s t : ℕ} (hst : s ≤ t) (htT : t ≤ T)
    (hEX : μ[X T] ≥ μ[X 0]) :
    μ[X t | 𝒢 s] =ᵐ[μ] X s := by
  -- First identify both `X t` and `X s` with the terminal conditional expectations from time `T`.
  have ht : μ[X T | 𝒢 t] =ᵐ[μ] X t :=
    condExp_terminal_ae_eq_self_of_expectation_ge hX htT hEX
  have hs : μ[X T | 𝒢 s] =ᵐ[μ] X s :=
    condExp_terminal_ae_eq_self_of_expectation_ge hX (Nat.le_trans hst htT) hEX
  -- Then rewrite through the tower property for conditional expectation.
  calc
    μ[X t | 𝒢 s] =ᵐ[μ] μ[μ[X T | 𝒢 t] | 𝒢 s] := by
      exact condExp_congr_ae ht.symm
    _ =ᵐ[μ] μ[X T | 𝒢 s] :=
      condExp_condExp_of_le (𝒢.mono hst) (𝒢.le t)
    _ =ᵐ[μ] X s := hs

-- Proof sketch: for fixed `s ≤ t`, choose `N` with `t ≤ T N` using `T N → ∞`, apply the previous
-- finite-horizon equality theorem with horizon `T N`, and conclude that all defining
-- conditional-expectation inequalities of the supermartingale are equalities.
/-- Theorem 9.32 (6): If `μ[X (T N)] ≥ μ[X 0]` along a sequence of times tending to infinity,
then the supermartingale is in fact a martingale. -/
theorem supermartingale_martingale_of_expectation_ge_along_subsequence
    [SigmaFiniteFiltration μ 𝒢] (hX : Supermartingale X 𝒢 μ) {T : ℕ → ℕ}
    (hT : Tendsto T atTop atTop) (hEX : ∀ N, μ[X (T N)] ≥ μ[X 0]) :
    Martingale X 𝒢 μ := by
  refine ⟨hX.stronglyAdapted, ?_⟩
  intro s t hst
  -- Choose a subsequence horizon that lies beyond the requested time `t`.
  obtain ⟨N, -, htN⟩ := Filter.exists_le_of_tendsto_atTop hT 0 t
  -- The finite-horizon equality theorem at time `T N` gives the martingale identity.
  exact supermartingale_condExp_ae_eq_of_expectation_ge hX hst htN (hEX N)

end Nat

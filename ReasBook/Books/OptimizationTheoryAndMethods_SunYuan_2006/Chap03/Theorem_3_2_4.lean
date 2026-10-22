/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Convex.Extrema
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Order.Filter.Extr

import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Theorem_1_3_19
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Algorithm_3_2_3

noncomputable section

open Filter

-- Domain sampling for this refine pass:
-- * primary domain: finite-run stationarity and nonterminating-run accumulation-point minimizer
--   statements for the Chapter 3 damped Newton method on `ℝⁿ`;
-- * inspected owner declarations:
--   - `NewtonMethodWithLineSearch` in `Algorithm_3_2_3`;
--   - `NewtonMethodWithLineSearch.DoesNotTerminate` / `terminatedAt` in `Algorithm_3_2_3`;
--   - `IsStationaryPoint` in `Chapter01/Definition_1_4_7`;
--   - `HasLowerLevelHessianLowerBound` / `lowerLevelSetOn` in `Chapter01/Theorem_1_3_19`;
--   - `IsMinOn` as the canonical minimizer owner and the Chapter 3 stronger companion
--     `newtonSequence_tendsto_minimizer` in `Theorem_3_2_5`.
--
-- Best owner abstraction:
-- * source-facing owner: `NewtonMethodWithLineSearch`;
-- * derived canonical owners: `IsStationaryPoint` for the finite zero-tolerance branch and
--   `IsMinOn` for the infinite-run minimizer conclusion on the regularity domain `D`.
--
-- Primitive data vs derived API:
-- * primitive data live in the algorithm owner itself: iterates, gradients, Hessians,
--   line-search data, the nonnegative stopping tolerance, the stop test `terminatedAt`, and the
--   stronger nontermination owner `DoesNotTerminate`;
-- * this file only adds the source-facing zero-tolerance finite-run hypothesis and the
--   lower-level-set Hessian hypotheses needed for Theorem 3.2.4;
-- * the nonterminating clause is kept at the accumulation-point layer rather than the stronger
--   full-sequence convergence layer of `Theorem_3_2_5`;
-- * part `(2)` keeps only the source accumulation-point data on the labeled theorem surface;
--   the required lower-level-set bookkeeping is pushed into a bridge theorem that derives
--   eventual membership in `lowerLevelSetOn D f A.x0` from openness of `D`, convergence to
--   `xStar ∈ D`, and the owner-level exact-line-search monotonicity lemma
--   `NewtonMethodWithLineSearch.objective_nonincreasing_step`;
-- * the stronger theorem `newtonSequence_tendsto_minimizer` from `Theorem_3_2_5` remains a
--   companion, not a replacement, because it adds the extra decrease assumption `(3.2.13)`;
-- * source/core/bridge triage for part `(2)`:
--   source-facing = accumulation points of a genuinely nonterminating damped Newton run together
--   with the source-level regularity assumptions on `D`,
--   core/canonical = `IsMinOn f D xStar`,
--   bridge/view = eventual sampled membership in `lowerLevelSetOn D f A.x0` derived from the
--   run and convergence data; any later result upgrading `IsMinOn f D xStar` to
--   `IsMinOn f Set.univ xStar` must be stated separately from this theorem.

section

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

section Theorem324Finite

variable {f : Point → ℝ} (A : NewtonMethodWithLineSearch n f)

/-- Chapter03 Theorem 3.2.4 (1). If the run of Algorithm 3.2.3 generated from `A.x0`
is finite and the stopping tolerance is zero, then some terminal iterate is a stationary
point of `f`. The implementation-level equality `A.g k = 0` is kept upstream as an auxiliary
recorded-gradient fact, while the theorem here uses the canonical Chapter 1 owner
`IsStationaryPoint` together with the source-facing Chapter 3 terminal-index owner
`A.IsTerminalIndex k`. -/
theorem dampedNewton_finiteRun_hasTerminalStationaryPoint
    (_hε : A.ε = 0)
    (_hFinite : A.IsFiniteSequence) :
    ∃ k, A.IsTerminalIndex k ∧ IsStationaryPoint f (A k) :=
  match _hFinite with
  | ⟨k, hk⟩ => ⟨k, hk, A.isStationaryPoint_of_terminatedAt_zeroTolerance _hε hk.1⟩

end Theorem324Finite

section Theorem324Convergence

variable {f : Point → ℝ} {D : Set Point} (A : NewtonMethodWithLineSearch n f)
variable
    (hD_open : IsOpen D)
    (hD_convex : Convex ℝ D)
    (hC2 : ContDiffOn ℝ 2 f D)
    (hLevelHessian : ∃ m > 0, HasLowerLevelHessianLowerBound D f A.x0 m)

/-- Exact line search makes the objective values along a genuinely nonterminating Newton run stay
below the initial value `f A.x0`. -/
theorem NewtonMethodWithLineSearch.objective_le_initial_of_doesNotTerminate
    (hNoTerminate : A.DoesNotTerminate) (k : ℕ) :
    f (A k) ≤ f A.x0 :=
  Nat.rec
    (by simpa [NewtonMethodWithLineSearch.coe_apply, A.x_zero])
    (fun k ih ↦
      let hk : A.ε < ‖A.g k‖ := lt_of_not_ge (hNoTerminate k)
      le_trans (A.objective_nonincreasing_step hk) ih)
    k

/-- If a subsequence of a genuinely nonterminating Newton run converges to `xStar ∈ D`, then the
sampled iterates eventually lie in the canonical anchored lower level set
`lowerLevelSetOn D f A.x0`. This packages the domain and objective-value bookkeeping needed by
the lower-level-set Hessian owner into a bridge lemma, rather than exposing it on the main
Theorem 3.2.4 statement. -/
theorem NewtonMethodWithLineSearch.eventually_subseq_mem_lowerLevelSetOn_of_tendsto
    (hD_open : IsOpen D)
    (hNoTerminate : A.DoesNotTerminate)
    {xStar : Point} {φ : ℕ → ℕ}
    (hxStar : xStar ∈ D)
    (hTendsto : Tendsto (A ∘ φ) atTop (nhds xStar)) :
    ∀ᶠ k in atTop, A (φ k) ∈ lowerLevelSetOn D f A.x0 :=
  let hEventuallyMemD : ∀ᶠ k in atTop, A (φ k) ∈ D :=
    hTendsto.eventually (hD_open.mem_nhds hxStar)
  hEventuallyMemD.mono fun k hkD ↦
    (mem_lowerLevelSetOn D f A.x0 (A (φ k))).2
      ⟨hkD, A.objective_le_initial_of_doesNotTerminate hNoTerminate (φ k)⟩

/-- Primitive accumulation-point minimizer conclusion for Theorem 3.2.4 (2): once the sampled
subsequence of a genuinely nonterminating damped Newton run is known to enter the canonical lower
level set `lowerLevelSetOn D f A.x0` eventually, any accumulation point `xStar ∈ D` of that
subsequence is a minimizer of `f` on `D`. This keeps the core theorem-level input at the
lower-level-set owner rather than storing run-specific domain bookkeeping as primitive data. -/
theorem dampedNewton_accumulationPoint_isMinOn_of_eventually_mem_lowerLevelSetOn
    (hNoTerminate : A.DoesNotTerminate)
    {xStar : Point} {φ : ℕ → ℕ}
    (hxStar : xStar ∈ D)
    (hφ : StrictMono φ)
    (hTendsto : Tendsto (A ∘ φ) atTop (nhds xStar))
    (hEventuallyLevel : ∀ᶠ k in atTop, A (φ k) ∈ lowerLevelSetOn D f A.x0) :
    IsMinOn f D xStar := sorry

/-- Chapter03 Theorem 3.2.4 (2). If the run of Algorithm 3.2.3 generated from `A.x0` never
satisfies its stop test, and the Chapter 1 open/convex/regularity/lower-level-set Hessian
hypotheses hold on `D`, then every accumulation point `xStar ∈ D` of the Newton iterates is a
minimizer of `f` on `D`. This keeps the labeled source-facing theorem at the accumulation-point
layer and avoids collapsing it into the stronger full-sequence convergence statement of
`Theorem_3_2_5`. The nontermination hypothesis is phrased with the algorithm owner's source stop
test `terminatedAt`, not with the weaker no-constant-tail predicate `IsInfiniteSequence`, because
the textbook meaning is that the Newton run remains active at every index. The lower-level-set
membership needed by the Chapter 1 Hessian-bound owner is derived internally from openness of
`D`, convergence to `xStar ∈ D`, and exact-line-search monotonicity, so the theorem surface no
longer asks users to provide a separate iterate-in-`D` bookkeeping hypothesis. -/
theorem dampedNewton_accumulationPoint_isMinOn
    (hNoTerminate : A.DoesNotTerminate)
    {xStar : Point} {φ : ℕ → ℕ}
    (hxStar : xStar ∈ D)
    (hφ : StrictMono φ)
    (hTendsto : Tendsto (A ∘ φ) atTop (nhds xStar)) :
    IsMinOn f D xStar :=
  let hEventuallyLevel :
      ∀ᶠ k in atTop, A (φ k) ∈ lowerLevelSetOn D f A.x0 :=
    A.eventually_subseq_mem_lowerLevelSetOn_of_tendsto hD_open hNoTerminate hxStar hTendsto
  A.dampedNewton_accumulationPoint_isMinOn_of_eventually_mem_lowerLevelSetOn
    hD_open hD_convex hC2 hLevelHessian hNoTerminate hxStar hφ hTendsto hEventuallyLevel

end Theorem324Convergence

end

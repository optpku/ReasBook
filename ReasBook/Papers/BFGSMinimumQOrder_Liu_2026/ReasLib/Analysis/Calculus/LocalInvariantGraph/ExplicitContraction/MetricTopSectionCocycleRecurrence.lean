module

-- The cocycle recurrence for the top iterated-derivative section of the metric fixed graph.
-- Built on the (undivided) master identity `MetricTopSectionMasterIdentity` and the center-map
-- derivative estimates in `MetricTopSectionSecantKernel`.  This leaf divides the master identity by
-- `(Φ′u)^m ≠ 0` to expose the self-referential cocycle form
--   `W (Φ u) = (Φ′u)⁻ᵐ • ( L (W u) + iteratedDeriv m g u − Σ[ζ-remainder] )`,
-- where `W = iteratedDeriv m ζ`, `Φ = centerMap ζ`, `g u = (R (u, ζ u)).2`.  The linear-in-`W u`
-- part is `(Φ′u)⁻ᵐ • L (W u)`; its operator norm is `≤ rate · lower⁻ᵐ`, and the change of
-- variables `u ↦ Φ u` contributes the extra `lower⁻¹`, giving the bunching factor
-- `rate · lower⁻⁽ᵐ⁺¹⁾ < 1`.  The fiber term and the `ζ`-remainder are strictly lower order (fed to
-- the `o(t)` bucket of the secant-defect recurrence).
public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricTopSectionMasterIdentity
public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricTopSectionSecantKernel
public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricFiberFaaDiBruno

public section
noncomputable section
open scoped NNReal Topology
open Filter Set
universe u
namespace LocalInvariantGraph
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- **Solved cocycle recurrence for the top iterated-derivative section.**  Dividing the undivided
master identity `iteratedDeriv_fixedGraph_master_identity` by `(Φ′u)^m ≠ 0`, the top jet
`W (Φ u) = iteratedDeriv m ζ (Φ u)` is expressed as `(Φ′u)⁻ᵐ` times the linear self-reference
`L (W u)` plus the fiber remainder derivative and minus the (strictly lower order) Faà-di-Bruno
`ζ`-remainder.  Requires `ζ ∈ Cᵐ` (`hprev`), `m ≤ d.nu`, and `C¹`-regularity of `ζ` for the
nonvanishing of `Φ′`. -/
theorem iteratedDeriv_fixedGraph_cocycle_solved
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ)
    (m : ℕ) (hmν : m ≤ d.nu) (hprev : ContDiff ℝ m (ζ : ℝ → X))
    (hζ1 : ContDiff ℝ 1 (ζ : ℝ → X)) (u : ℝ) :
    iteratedDeriv m (ζ : ℝ → X) (d.centerMap ζ u)
      = (deriv (d.centerMap ζ) u)⁻¹ ^ m •
          (d.L (iteratedDeriv m (ζ : ℝ → X) u)
            + iteratedDeriv m (fun w ↦ (d.R (w, (ζ : ℝ → X) w)).2) u
            - ∑ c ∈ (Finset.univ.filter (fun c : OrderedFinpartition m ↦ c.length ≠ m)),
                iteratedFDeriv ℝ c.length (ζ : ℝ → X) (d.centerMap ζ u)
                  (fun j ↦ iteratedDeriv (c.partSize j) (d.centerMap ζ) u)) := by
  -- Abbreviation for `Φ' := deriv (centerMap ζ) u`; keep the analytic blocks explicit so the goal
  -- pattern-matches directly.
  set Φ' := deriv (d.centerMap ζ) u with hΦ'
  -- The master identity: `Φ'^m • (iteratedDeriv m ζ (Φu)) + rem = L (iteratedDeriv m ζ u) + gᵐ`.
  have hmaster := iteratedDeriv_fixedGraph_master_identity d ζ hfixed m hmν hprev u
  -- Nonvanishing of Φ'.
  have hΦ'_ne : Φ' ≠ 0 := centerMap_deriv_ne_zero d ζ hζ1 u
  have hpow_ne : Φ' ^ m ≠ 0 := pow_ne_zero m hΦ'_ne
  -- Rearrange the master identity to solve for `Φ'^m • (iteratedDeriv m ζ (Φu))`.
  have hsolve : Φ' ^ m • iteratedDeriv m (ζ : ℝ → X) (d.centerMap ζ u)
      = d.L (iteratedDeriv m (ζ : ℝ → X) u)
        + iteratedDeriv m (fun w ↦ (d.R (w, (ζ : ℝ → X) w)).2) u
        - ∑ c ∈ (Finset.univ.filter (fun c : OrderedFinpartition m ↦ c.length ≠ m)),
            iteratedFDeriv ℝ c.length (ζ : ℝ → X) (d.centerMap ζ u)
              (fun j ↦ iteratedDeriv (c.partSize j) (d.centerMap ζ) u) :=
    eq_sub_of_add_eq hmaster
  -- Divide by `Φ'^m`: substitute `hsolve` on the right, then cancel `Φ'⁻¹^m • Φ'^m = 1`.
  rw [← hsolve, inv_pow, smul_smul, inv_mul_cancel₀ hpow_ne, one_smul]

end LocalInvariantGraph

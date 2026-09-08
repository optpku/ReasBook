module

-- Steps 9-10: continuity of the top section + the finite-smoothness bootstrap driver.
-- Built on the packaging in `MetricTopSectionHolonomicAssembly` (`topSectionValue`,
-- `hasFDerivAt_iteratedFDeriv_of_hasDerivAt`).  This file adds the continuity reduction
-- `Continuous a ⇐ Continuous v` and the per-order induction that produces the frozen
-- `topSection` obligation from the abstract secant core.
public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricTopSectionHolonomicAssembly
public import ReasLib.Analysis.Calculus.LocalCutoff.GraphJetTransform.FixedGraphContext
public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricPicardCertificate
public import ReasLib.Analysis.Calculus.LocalCutoff.GraphJetTransform.HolonomicTopSection
public import Mathlib.Analysis.Normed.Module.Multilinear.Curry
public import Mathlib.Analysis.Normed.Operator.Bilinear

public section

noncomputable section

open scoped NNReal Topology
open Filter Set

universe u

namespace LocalInvariantGraph

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-! ## Step 9: continuity of the multilinear top section.

The section value `topSectionValue m v = (smulRight 1 (piFieldEquiv v)).uncurryLeft` is built from
`v` by continuous (in fact linear) constructions, so `u ↦ topSectionValue m (v u)` is continuous as
soon as `v` is.  (The name `continuous_topJetSectionValue` is retained for the downstream adapter.) -/

/-- Continuity of `u ↦ topSectionValue m (v u)` reduces to continuity of `v`.  The map factors
through `piFieldEquiv` (a linear isometry equiv), `smulRight 1 ·` (a continuous linear map), and
`uncurryLeft` (the inverse leg of the curry isometry equiv). -/
theorem continuous_topJetSectionValue (m : ℕ) (v : ℝ → X) (hv : Continuous v) :
    Continuous (fun u ↦ topSectionValue m (v u)) :=
  -- Delegate to the assembly layer's continuity lemma (same construction; the inline re-derivation
  -- fails to infer the `[×(m+1)]` multilinear family at `.uncurryLeft`).
  continuous_topSectionValue m v hv

/-! ## The abstract secant core (kernel deliverable), and the finite-smoothness driver. -/

/-- The core secant deliverable (the recurrence kernel), stated abstractly so this driver builds
independently of the kernel file: for every order `m` strictly below `d.nu`, given the previous
smoothness `ContDiff ℝ m ζ`, a continuous derivative-value section `v` witnessing the pointwise
`HasDerivAt` of the scalar top iterated derivative. -/
def MetricTopSectionCore (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope) : Prop :=
  ∀ m : ℕ, m < d.nu → ContDiff ℝ m (ζ : ℝ → X) →
    ∃ v : ℝ → X, Continuous v ∧
      ∀ u, HasDerivAt (iteratedDeriv m (ζ : ℝ → X)) (v u) u

/-- Package a core tuple at order `m = r - 1` into the holonomic `topSection` obligation for
order `r`, in the exact `∃ a, Continuous a ∧ ∀ u, HasFDerivAt … ((a u).curryLeft) u` shape. -/
theorem topSectionWitness_of_core
    (ζ : ℝ → X)
    {r : ℕ} (hr : 1 ≤ r)
    (v : ℝ → X) (hv : Continuous v)
    (hderiv : ∀ u, HasDerivAt (iteratedDeriv (r - 1) ζ) (v u) u) :
    ∃ a : ℝ → (ℝ [×(r - 1 + 1)]→L[ℝ] X),
      Continuous a ∧
        ∀ u, HasFDerivAt (fun y ↦ (ftaylorSeries ℝ ζ y) (r - 1))
          ((a u).curryLeft) u := by
  refine ⟨fun u ↦ topSectionValue (r - 1) (v u), continuous_topJetSectionValue (r - 1) v hv, ?_⟩
  intro u
  exact hasFDerivAt_iteratedFDeriv_of_hasDerivAt (r - 1) ζ v u (hderiv u)

/-- The finite-smoothness induction: from the core, `ζ ∈ C^r` for every `r ≤ d.nu`.  Order `m`'s
smoothness is established before order `m + 1`'s witness consumes it, so this is not circular. -/
theorem contDiff_le_of_core
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hcore : MetricTopSectionCore d ζ) :
    ∀ r : ℕ, r ≤ d.nu → ContDiff ℝ r (ζ : ℝ → X) := by
  intro r
  induction r with
  | zero => intro _; exact contDiff_zero.mpr ζ.1.continuous
  | succ r ih =>
      intro hrν
      have hr_le : r ≤ d.nu := (Nat.le_succ r).trans hrν
      have hr_lt : r < d.nu := Nat.lt_of_succ_le hrν
      have hprev : ContDiff ℝ r (ζ : ℝ → X) := ih hr_le
      obtain ⟨v, hv, hderiv⟩ := hcore r hr_lt hprev
      have hr1 : 1 ≤ r + 1 := Nat.succ_le_succ (Nat.zero_le r)
      -- `(r + 1) - 1 = r` holds definitionally in `ℕ`, so `hprev`/`hderiv` fit the order-`r+1`
      -- witness and the successor criterion directly.
      have hderiv' : ∀ u, HasDerivAt (iteratedDeriv ((r + 1) - 1) (ζ : ℝ → X)) (v u) u := hderiv
      have hprev' : ContDiff ℝ ((r + 1) - 1) (ζ : ℝ → X) := hprev
      obtain ⟨a, ha, hderivF⟩ := topSectionWitness_of_core (ζ : ℝ → X) hr1 v hv hderiv'
      exact LocalCutoff.GraphTransform.contDiff_succ_of_holonomic_topSection hr1 hprev' a ha hderivF

/-- The `topSection` witness at a single order `r`: establish `ζ ∈ C^{r-1}` from the core (via the
induction), then package the core tuple at order `r - 1`.  This is exactly the frozen certificate
field `topSection` at order `r`. -/
theorem topSectionWitness_at_of_core
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hcore : MetricTopSectionCore d ζ)
    {r : ℕ} (hr : 1 ≤ r) (hrν : r ≤ d.nu) :
    ∃ a : ℝ → (ℝ [×(r - 1 + 1)]→L[ℝ] X),
      Continuous a ∧
        ∀ u, HasFDerivAt (fun y ↦ (ftaylorSeries ℝ (ζ : ℝ → X) y) (r - 1))
          ((a u).curryLeft) u := by
  have hr_lt : r - 1 < d.nu :=
    lt_of_lt_of_le (Nat.sub_lt (lt_of_lt_of_le Nat.zero_lt_one hr) Nat.zero_lt_one) hrν
  have hprev : ContDiff ℝ (r - 1) (ζ : ℝ → X) :=
    contDiff_le_of_core d ζ hcore (r - 1) (le_trans (Nat.sub_le r 1) hrν)
  obtain ⟨v, hv, hderiv⟩ := hcore (r - 1) hr_lt hprev
  exact topSectionWitness_of_core (ζ : ℝ → X) hr v hv hderiv

/-- Helper for Infrastructure I.16a: an orderwise family of fixed-graph jet contexts supplies
the continuous derivative-value sections required by the metric top-section core. -/
theorem metricTopSectionCore_of_fixedGraphJetContexts
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (contexts : ∀ m : ℕ, m < d.nu →
      ContDiff ℝ m (ζ : ℝ → X) →
        LocalCutoff.GraphTransform.FixedGraphJetContext (m + 1) (ζ : ℝ → X)) :
    MetricTopSectionCore d ζ := by
  intro m hm hprev
  let context := contexts m hm hprev
  have hcont : ContDiff ℝ 1 (iteratedDeriv m (ζ : ℝ → X)) := by
    simpa only [Nat.add_sub_cancel] using context.predecessor_iteratedDeriv_contDiff_one
  rw [contDiff_one_iff_deriv] at hcont
  refine ⟨deriv (iteratedDeriv m (ζ : ℝ → X)), hcont.2, ?_⟩
  intro u
  exact (hcont.1 u).hasDerivAt

end LocalInvariantGraph

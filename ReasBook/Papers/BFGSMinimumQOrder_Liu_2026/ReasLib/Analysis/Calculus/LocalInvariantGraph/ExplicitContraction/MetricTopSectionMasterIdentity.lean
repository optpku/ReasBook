module

public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricTopSectionFaaDiBruno

public section
noncomputable section
open scoped NNReal Topology
open Filter Set
universe u
namespace LocalInvariantGraph
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Master differentiated identity for the metric fixed graph.  Differentiating the fixed-point
equation `ζ ∘ Φ = L ∘ ζ + g` (Φ := centerMap ζ, g u := (R (u,ζu)).2) `m` times and isolating the
Faà-di-Bruno atomic term gives, after solving for `S (Φ u)` (Φ′ ≠ 0 is NOT needed here — this is the
un-divided form): -/
theorem iteratedDeriv_fixedGraph_master_identity
    [CompleteSpace X]
    (d : MetricGraphTransformData X)
    (ζ : SmallLipschitzGraph X d.radius d.slope)
    (hfixed : d.transform ζ = ζ)
    (m : ℕ) (hmν : m ≤ d.nu) (hprev : ContDiff ℝ m (ζ : ℝ → X)) (u : ℝ) :
    (deriv (d.centerMap ζ) u) ^ m • iteratedDeriv m (ζ : ℝ → X) (d.centerMap ζ u)
      + (∑ c ∈ (Finset.univ.filter (fun c : OrderedFinpartition m ↦ c.length ≠ m)),
          iteratedFDeriv ℝ c.length (ζ : ℝ → X) (d.centerMap ζ u)
            (fun j ↦ iteratedDeriv (c.partSize j) (d.centerMap ζ) u))
      = d.L (iteratedDeriv m (ζ : ℝ → X) u) + iteratedDeriv m (fun w ↦ (d.R (w, (ζ : ℝ → X) w)).2) u := by
  -- Coerce the regularity budget to `WithTop ℕ∞`.
  have hmν_top : (m : WithTop ℕ∞) ≤ d.nu := by
    exact_mod_cast hmν
  -- Step 1: K1's atomic split collapses the LHS to `iteratedDeriv m (ζ ∘ Φ) u`.
  have hK1 := iteratedDeriv_zeta_comp_centerMap_atomic_split d ζ m hmν hprev u
  -- Step 2: the fixed-point equation, re-derived inline as a function identity.
  have hfeq : ((ζ : ℝ → X) ∘ d.centerMap ζ)
      = fun w ↦ d.L ((ζ : ℝ → X) w) + (d.R (w, (ζ : ℝ → X) w)).2 := by
    funext w
    simpa [Function.comp_apply] using d.fixedGraph_equation ζ hfixed w
  -- Smoothness of the two summands of the RHS function.
  have hRsmooth : ContDiff ℝ m (fun w : ℝ ↦ (d.R (w, (ζ : ℝ → X) w)).2) := by
    have hpair : ContDiff ℝ m (fun w : ℝ ↦ (w, (ζ : ℝ → X) w)) :=
      contDiff_id.prodMk hprev
    have hR : ContDiff ℝ m d.R := d.hR_smooth.of_le hmν_top
    exact contDiff_snd.comp (hR.comp hpair)
  have hLsmooth : ContDiff ℝ m (fun w : ℝ ↦ d.L ((ζ : ℝ → X) w)) :=
    (d.L).contDiff.comp hprev
  -- Step 3a: the continuous linear map `d.L` commutes with `iteratedDeriv`.
  have hLcomm : iteratedDeriv m (fun w : ℝ ↦ d.L ((ζ : ℝ → X) w)) u
      = d.L (iteratedDeriv m (ζ : ℝ → X) u) := by
    have hfd := (d.L).iteratedFDeriv_comp_left (f := (ζ : ℝ → X)) (x := u)
      hprev.contDiffAt (le_rfl)
    rw [iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_eq_iteratedFDeriv,
      show (fun w : ℝ ↦ d.L ((ζ : ℝ → X) w)) = (d.L ∘ (ζ : ℝ → X)) from rfl, hfd]
    simp [ContinuousLinearMap.compContinuousMultilinearMap_coe]
  -- Step 3b: push `iteratedDeriv m` through the sum on the RHS.
  have hsum : iteratedDeriv m
        (fun w ↦ d.L ((ζ : ℝ → X) w) + (d.R (w, (ζ : ℝ → X) w)).2) u
      = iteratedDeriv m (fun w : ℝ ↦ d.L ((ζ : ℝ → X) w)) u
        + iteratedDeriv m (fun w : ℝ ↦ (d.R (w, (ζ : ℝ → X) w)).2) u := by
    have hadd := iteratedDeriv_add (f := fun w : ℝ ↦ d.L ((ζ : ℝ → X) w))
      (g := fun w : ℝ ↦ (d.R (w, (ζ : ℝ → X) w)).2) (n := m) (x := u)
      hLsmooth.contDiffAt hRsmooth.contDiffAt
    -- `(fun w ↦ f w + g w) = f + g` definitionally; rewrite so `iteratedDeriv_add` applies.
    have hfun : (fun w ↦ d.L ((ζ : ℝ → X) w) + (d.R (w, (ζ : ℝ → X) w)).2)
        = (fun w : ℝ ↦ d.L ((ζ : ℝ → X) w)) + (fun w : ℝ ↦ (d.R (w, (ζ : ℝ → X) w)).2) := rfl
    rw [hfun]
    exact hadd
  -- Assemble.
  rw [← hK1, hfeq, hsum, hLcomm]

end LocalInvariantGraph

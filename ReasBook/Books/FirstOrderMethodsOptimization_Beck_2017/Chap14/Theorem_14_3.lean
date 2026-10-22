/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap14.Theorem_14_3_Helpers.Recovery

universe u

open Filter
open scoped Topology

section

variable {p : ℕ} {Ei : Fin p → Type u}
variable [∀ i, PseudoMetricSpace (Ei i)]

/-- Local recovery condition needed to pass a strict one-block improvement at a cluster point to
nearby base points. This is the exact condition consumed by the canonical Theorem 14.3 helper
chain. -/
def AlternatingMinimizationStrictCompetitorRecovery
    (F : ((i : Fin p) → Ei i) → EReal) : Prop :=
  ∀ {xBar : (i : Fin p) → Ei i},
    xBar ∈ effective_domain F →
      ∀ (i : Fin p) ⦃zi : Ei i⦄,
        Function.update xBar i zi ∈ effective_domain F →
          F (Function.update xBar i zi) < F xBar →
            ∀ s ∈ 𝓝 zi,
              {xBase |
                  ∃ zi' ∈ s,
                    Function.update xBase i zi' ∈ effective_domain F ∧
                      F (Function.update xBase i zi') < F xBar} ∈
                𝓝 xBar

/-- Corollary of Theorem 14.3: under the theorem hypotheses, including strict-competitor recovery,
every sequential limit point of the alternating-minimization trajectory is a coordinate-wise
minimum of `F`; effective-domain membership is part of that owner predicate. The uniqueness
hypothesis keeps only the source-essential subsingleton clause for each block argmin set, because
nonemptiness is derived separately from `hclosed` and `hlevel`. -/
theorem alternating_minimization_cluster_points_coordinatewise_minima
    [ProperSpace ((i : Fin p) → Ei i)]
    (F : ((i : Fin p) → Ei i) → EReal)
    (x : ℕ → (i : Fin p) → Ei i)
    (hclosed : LowerSemicontinuous F)
    (hcont : ContinuousOn F (effective_domain F))
    (hunique :
      ∀ xBar ∈ effective_domain F, ∀ i : Fin p,
        Set.Subsingleton (alternating_minimization_argmin F xBar i))
    (hlevel : ∀ α : ℝ, Bornology.IsBounded {x | F x ≤ (α : EReal)})
    (hrecover : AlternatingMinimizationStrictCompetitorRecovery F)
    (htraj : is_alternating_minimization_trajectory F x)
    (xBar : (i : Fin p) → Ei i)
    (hxBar : MapClusterPt xBar atTop x) :
    is_coordinatewise_minimum F xBar := by
  have hxBar_dom :
      xBar ∈ effective_domain F :=
    AlternatingMinimization.ClusterPoint.mem_effective_domain_of_initial_sublevel
      F x hclosed htraj hxBar
  rcases alternating_minimization_prefix_state_stage_induction_invariant
      F x hclosed hcont hunique hlevel htraj hrecover hxBar p (le_rfl : p ≤ p) with
    ⟨ψ, hψ, hiter, hstage, hblocks⟩
  refine ⟨hxBar_dom, ?_⟩
  intro i
  exact (mem_alternating_minimization_argmin_iff).1 (hblocks i i.is_lt)

/-- Theorem 14.3 [Convergence of alternating minimization to coordinate-wise minima]: let
`F : E₁ × ... × E_p → (-∞, ∞]` be closed and continuous on its effective domain, assume that each
one-block subproblem has a unique minimizer and that every real sublevel set of `F` is bounded,
and let `x` be an alternating-minimization trajectory for `F`. Then the trajectory is bounded,
and every sequential limit point of `x` is a coordinate-wise minimum of `F`. The source's
properness clause for `F` is redundant for this conclusion and is not part of the exported Lean
API; the generalized Lean theorem still keeps the ambient `ProperSpace ((i : Fin p) → Ei i)`
hypothesis explicit because the cluster-point argument uses compactness of closed bounded
sublevels. On the Lean surface, `hunique` asks only for subsingleton block argmin sets, since the
    existing closedness and bounded-sublevel hypotheses already supply the needed nonemptiness.
The explicit recovery hypothesis records the domain-stability step used by the canonical helper
chain and prevents applying the result to extended-valued domains where strict block competitors
cannot be approximated from nearby base points. -/
theorem alternating_minimization_convergence_to_coordinatewise_minima
    [ProperSpace ((i : Fin p) → Ei i)]
    (F : ((i : Fin p) → Ei i) → EReal)
    (x : ℕ → (i : Fin p) → Ei i)
    (hclosed : LowerSemicontinuous F)
    (hcont : ContinuousOn F (effective_domain F))
    (hunique :
      ∀ xBar ∈ effective_domain F, ∀ i : Fin p,
        Set.Subsingleton (alternating_minimization_argmin F xBar i))
    (hlevel : ∀ α : ℝ, Bornology.IsBounded {x | F x ≤ (α : EReal)})
    (hrecover : AlternatingMinimizationStrictCompetitorRecovery F)
    (htraj : is_alternating_minimization_trajectory F x) :
    Bornology.IsBounded (Set.range x) ∧
      ∀ xBar : (i : Fin p) → Ei i, MapClusterPt xBar atTop x →
        is_coordinatewise_minimum F xBar := by
  constructor
  · exact alternating_minimization_trajectory_range_bounded F x hlevel htraj
  · intro xBar hxBar
    exact alternating_minimization_cluster_points_coordinatewise_minima
      F x hclosed hcont hunique hlevel hrecover htraj xBar hxBar

end

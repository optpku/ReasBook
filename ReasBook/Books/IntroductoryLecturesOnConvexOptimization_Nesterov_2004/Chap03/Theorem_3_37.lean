/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

section Minimax

variable {X : Type u} {U : Type v}

variable [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
variable [TopologicalSpace U] [AddCommGroup U] [Module ℝ U]
  [IsTopologicalAddGroup U] [ContinuousSMul ℝ U]

/-
Theorem 3.37 lies in the chapter's compact convex-concave minimax domain.

Sampled owner-style declarations:
- mathlib `Sion.exists_isSaddlePointOn`, the real-valued compact convex-concave saddle-point
  owner;
- mathlib `ContinuousOn.lowerSemicontinuousOn` and `ContinuousOn.upperSemicontinuousOn`, the
  canonical slice-semicontinuity bridges extracted from continuity on `P × S`;
- mathlib `ConvexOn.quasiconvexOn` and `ConcaveOn.quasiconcaveOn`, the standard bridges from the
  source convex/concave slice hypotheses to the Sion owner assumptions.
- mathlib `IsLeast.csInf_eq` and `IsGreatest.csSup_eq`, the canonical order-theoretic bridges from
  attained extrema to the source `sInf`/`sSup` expressions.

Best owner abstraction:
- source-facing: the minimax equality between the upper and lower slice-value expressions on `P`
  and `S`;
- core/canonical: `Sion.exists_isSaddlePointOn`;
- bridge/view: the slice semicontinuity and quasiconvexity/quasiconcavity consequences of the
  source continuity and convexity/concavity hypotheses, together with the `IsLeast`/`IsGreatest`
  extremum identifications of the two value images.

Primitive data:
- the compact nonempty primal set `P`;
- the compact nonempty dual set `S`;
- the payoff `Ψ`;
- continuity of `Ψ` on `P × S`;
- convexity of the `x`-slices and concavity of the `u`-slices.

Derived API:
- convexity of `P` and `S`, recovered from one primal slice and one dual slice because the slice
  owners `ConvexOn` and `ConcaveOn` already bundle convexity of the feasible set;
- the upper slice-value function `x ↦ sSup ((fun u ↦ Ψ x u) '' S)`;
- the lower slice-value function `u ↦ sInf ((fun x ↦ Ψ x u) '' P)`;
- the minimax equality below.

This refinement keeps the source-facing equality but replaces the local proof-level wheel with a
direct specialization of the canonical owner `Sion.exists_isSaddlePointOn`. The only extra work
is to derive the owner hypotheses already latent in the source data, then collapse the resulting
saddle point to the textbook `sInf`/`sSup` equality through the canonical attained-extremum
bridges `IsLeast.csInf_eq` and `IsGreatest.csSup_eq`.
-/

/-- Theorem 3.37: for a continuous convex-concave payoff on compact nonempty sets `P` and `S`,
the infimum of the upper slice-value function `x ↦ sSup ((fun u ↦ Ψ x u) '' S)` over `P` equals
the supremum of the lower slice-value function `u ↦ sInf ((fun x ↦ Ψ x u) '' P)` over `S`. -/
theorem compact_convex_concave_minimax
    {P : Set X} {S : Set U} (hP_nonempty : P.Nonempty) (hS_nonempty : S.Nonempty)
    (hP_compact : IsCompact P) (hS_compact : IsCompact S)
    {Ψ : X → U → ℝ}
    (hΨ_cont : ContinuousOn (fun z : X × U ↦ Ψ z.1 z.2) (Set.prod P S))
    (hΨ_convex : ∀ u ∈ S, ConvexOn ℝ P (fun x ↦ Ψ x u))
    (hΨ_concave : ∀ x ∈ P, ConcaveOn ℝ S (fun u ↦ Ψ x u)) :
    sInf ((fun x ↦ sSup ((fun u ↦ Ψ x u) '' S)) '' P) =
      sSup ((fun u ↦ sInf ((fun x ↦ Ψ x u) '' P)) '' S) := by
  let u0 : U := hS_nonempty.choose
  have hu0 : u0 ∈ S := hS_nonempty.choose_spec
  let x0 : X := hP_nonempty.choose
  have hx0 : x0 ∈ P := hP_nonempty.choose_spec
  have hP_convex : Convex ℝ P := (hΨ_convex u0 hu0).1
  have hS_convex : Convex ℝ S := (hΨ_concave x0 hx0).1
  have hcont_x : ∀ u ∈ S, ContinuousOn (fun x ↦ Ψ x u) P := by
    intro u hu
    simpa using
      hΨ_cont.comp
        (show ContinuousOn (fun x : X ↦ (x, u)) P from continuousOn_id.prodMk continuousOn_const)
        (show Set.MapsTo (fun x : X ↦ (x, u)) P (Set.prod P S) from
          fun x hx ↦ ⟨hx, hu⟩)
  have hcont_u : ∀ x ∈ P, ContinuousOn (fun u ↦ Ψ x u) S := by
    intro x hx
    simpa using
      hΨ_cont.comp
        (show ContinuousOn (fun u : U ↦ (x, u)) S from continuousOn_const.prodMk continuousOn_id)
        (show Set.MapsTo (fun u : U ↦ (x, u)) S (Set.prod P S) from
          fun u hu ↦ ⟨hx, hu⟩)
  obtain ⟨xStar, hxStar, uStar, huStar, hsaddle⟩ :=
    Sion.exists_isSaddlePointOn
      hP_nonempty hP_convex hP_compact
      (fun u hu ↦ (hcont_x u hu).lowerSemicontinuousOn)
      (fun u hu ↦ (hΨ_convex u hu).quasiconvexOn)
      hS_convex hS_nonempty hS_compact
      (fun x hx ↦ (hcont_u x hx).upperSemicontinuousOn)
      (fun x hx ↦ (hΨ_concave x hx).quasiconcaveOn)
  have hupper_xStar : sSup ((fun u ↦ Ψ xStar u) '' S) = Ψ xStar uStar := by
    exact (show IsGreatest ((fun u ↦ Ψ xStar u) '' S) (Ψ xStar uStar) from by
      refine ⟨⟨uStar, huStar, rfl⟩, ?_⟩
      intro z hz
      rcases hz with ⟨u, hu, rfl⟩
      exact hsaddle xStar hxStar u hu).csSup_eq
  have hlower_uStar : sInf ((fun x ↦ Ψ x uStar) '' P) = Ψ xStar uStar := by
    exact (show IsLeast ((fun x ↦ Ψ x uStar) '' P) (Ψ xStar uStar) from by
      refine ⟨⟨xStar, hxStar, rfl⟩, ?_⟩
      intro z hz
      rcases hz with ⟨x, hx, rfl⟩
      exact hsaddle x hx uStar huStar).csInf_eq
  have hupper_least :
      IsLeast ((fun x ↦ sSup ((fun u ↦ Ψ x u) '' S)) '' P) (Ψ xStar uStar) := by
    refine ⟨⟨xStar, hxStar, hupper_xStar⟩, ?_⟩
    intro z hz
    rcases hz with ⟨x, hx, rfl⟩
    have hmem : Ψ x uStar ∈ (fun u ↦ Ψ x u) '' S := ⟨uStar, huStar, rfl⟩
    have hbdd : BddAbove ((fun u ↦ Ψ x u) '' S) :=
      (hS_compact.image_of_continuousOn (hcont_u x hx)).bddAbove
    exact le_trans (hsaddle x hx uStar huStar) (le_csSup hbdd hmem)
  have hlower_greatest :
      IsGreatest ((fun u ↦ sInf ((fun x ↦ Ψ x u) '' P)) '' S) (Ψ xStar uStar) := by
    refine ⟨⟨uStar, huStar, hlower_uStar⟩, ?_⟩
    intro z hz
    rcases hz with ⟨u, hu, rfl⟩
    have hmem : Ψ xStar u ∈ (fun x ↦ Ψ x u) '' P := ⟨xStar, hxStar, rfl⟩
    have hbdd : BddBelow ((fun x ↦ Ψ x u) '' P) :=
      (hP_compact.image_of_continuousOn (hcont_x u hu)).bddBelow
    exact le_trans (csInf_le hbdd hmem) (hsaddle xStar hxStar u hu)
  calc
    sInf ((fun x ↦ sSup ((fun u ↦ Ψ x u) '' S)) '' P) = Ψ xStar uStar := hupper_least.csInf_eq
    _ = sSup ((fun u ↦ sInf ((fun x ↦ Ψ x u) '' P)) '' S) := hlower_greatest.csSup_eq.symm

end Minimax

end

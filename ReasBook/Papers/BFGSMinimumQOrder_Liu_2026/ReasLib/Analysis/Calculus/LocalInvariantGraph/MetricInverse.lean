module

public import ReasLib.Topology.ContinuousMap.SmallLipschitzGraph.Transform
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn

public section

noncomputable section

open Set
open scoped NNReal

universe u

namespace LocalInvariantGraph

variable {X : Type u} [NormedAddCommGroup X]
variable {radius slope epsilon : ℝ≥0}

/-- The product max metric dominates each coordinate distance. -/
private theorem prod_fst_dist_le (p q : ℝ × X) : dist p.1 q.1 ≤ dist p q := by
  rw [Prod.dist_eq, Real.dist_eq]
  exact le_max_left _ _

/-- A Lipschitz perturbation along a graph of slope at most one makes its center
coordinate approximate the identity with the same Lipschitz constant. -/
theorem centerProjection_approximatesId
    (R : ℝ × X → ℝ × X) (hR : LipschitzWith epsilon R)
    (zeta : SmallLipschitzGraph X radius slope) (hslope : slope ≤ 1) :
    ApproximatesLinearOn
      (fun u : ℝ ↦ u + (R (u, zeta u)).1)
      (ContinuousLinearMap.id ℝ ℝ) univ epsilon := by
  -- The max product metric makes `u ↦ (u, zeta u)` nonexpanding when the
  -- graph slope is at most one.
  have hgraph : LipschitzWith 1 (fun u : ℝ ↦ (u, zeta u)) := by
    simpa only [Function.comp_def, id_eq, max_eq_left hslope] using
      LipschitzWith.id.prodMk (SmallLipschitzGraph.lipschitzWith zeta)
  -- Compose the remainder with that parametrization and project to the center.
  have hcenter : LipschitzWith epsilon (fun u : ℝ ↦ (R (u, zeta u)).1) := by
    simpa only [one_mul, mul_one, Function.comp_def] using
      LipschitzWith.prod_fst.comp (hR.comp hgraph)
  -- Subtracting the identity from the center map leaves precisely this center remainder.
  apply LipschitzOnWith.approximatesLinearOn
  rw [lipschitzOnWith_univ]
  convert hcenter using 1
  funext u
  simp only [Pi.sub_apply, ContinuousLinearMap.id_apply, add_sub_cancel_left]

/-- A center coordinate that is a perturbation of the identity by a Lipschitz
constant below one is represented by a global homeomorphism. -/
theorem exists_centerProjectionHomeomorph
    (R : ℝ × X → ℝ × X) (hR : LipschitzWith epsilon R)
    (zeta : SmallLipschitzGraph X radius slope) (hslope : slope ≤ 1)
    (hepsilon : epsilon < 1) :
    ∃ e : ℝ ≃ₜ ℝ, (e : ℝ → ℝ) = fun u ↦ u + (R (u, zeta u)).1 := by
  -- Feed the approximation estimate to the global inverse theorem for the
  -- identity continuous linear equivalence.
  have happrox := centerProjection_approximatesId R hR zeta hslope
  have hsmall : Subsingleton ℝ ∨
      epsilon < ‖((ContinuousLinearEquiv.refl ℝ ℝ).symm : ℝ →L[ℝ] ℝ)‖₊⁻¹ := by
    right
    simpa using hepsilon
  refine ⟨happrox.toHomeomorph _ hsmall, ?_⟩
  rfl

/-- The center coordinate along a graph is quantitatively injective when its
Lipschitz perturbation size leaves a positive lower bound. -/
theorem antilipschitzWith_centerProjection
    (R : ℝ × X → ℝ × X) (hR : LipschitzWith epsilon R)
    (zeta : SmallLipschitzGraph X radius slope) (hslope : slope ≤ 1)
    (lower : ℝ≥0) (hlower : 0 < lower) (hlower_add : lower + epsilon = 1) :
    AntilipschitzWith lower⁻¹ (fun u : ℝ ↦ u + (R (u, zeta u)).1) := by
  -- The positive unused part of the unit rate verifies the inverse theorem's
  -- strict smallness condition.
  have hepsilon : epsilon < 1 := by
    rw [← hlower_add]
    exact lt_add_of_pos_left epsilon hlower
  have hsmall : Subsingleton ℝ ∨
      epsilon < ‖((ContinuousLinearEquiv.refl ℝ ℝ).symm : ℝ →L[ℝ] ℝ)‖₊⁻¹ := by
    right
    simpa only [ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.coe_refl,
      ContinuousLinearMap.nnnorm_id, inv_one] using hepsilon
  -- Normalize the approximation theorem's rate `(‖id⁻¹‖⁻¹ - epsilon)⁻¹`
  -- to the named lower bound.
  have hanti := (centerProjection_approximatesId R hR zeta hslope).antilipschitz hsmall
  have hnorm : ‖((ContinuousLinearEquiv.refl ℝ ℝ).symm : ℝ →L[ℝ] ℝ)‖₊ =
      (1 : ℝ≥0) := by
    rw [ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.coe_refl,
      ContinuousLinearMap.nnnorm_id]
  have hparam :
      (‖((ContinuousLinearEquiv.refl ℝ ℝ).symm : ℝ →L[ℝ] ℝ)‖₊⁻¹ - epsilon)⁻¹ =
        lower⁻¹ := by
    rw [hnorm, inv_one, ← hlower_add, add_tsub_cancel_right]
  rw [hparam] at hanti
  have hrestrict :
      AntilipschitzWith lower⁻¹ (fun u : ℝ ↦ u + (R (u, zeta u)).1) := by
    rw [antilipschitzWith_iff_le_mul_dist]
    intro x y
    have hxy := hanti.le_mul_dist (⟨x, Set.mem_univ x⟩) (⟨y, Set.mem_univ y⟩)
    simpa only [Set.restrict_apply, Set.mem_univ, Subtype.dist_eq] using hxy
  exact hrestrict

/-- The inverse of the center coordinate along a graph has Lipschitz constant
given by the reciprocal center lower bound. -/
theorem lipschitzWith_invFun_centerProjection
    (R : ℝ × X → ℝ × X) (hR : LipschitzWith epsilon R)
    (zeta : SmallLipschitzGraph X radius slope) (hslope : slope ≤ 1)
    (lower : ℝ≥0) (hlower : 0 < lower) (hlower_add : lower + epsilon = 1) :
    LipschitzWith lower⁻¹
      (Function.invFun (fun u : ℝ ↦ u + (R (u, zeta u)).1)) := by
  -- Surjectivity makes `invFun` a right inverse, and the antilipschitz bound
  -- turns every right inverse into a Lipschitz map.
  have happrox := centerProjection_approximatesId R hR zeta hslope
  have hepsilon : epsilon < 1 := by
    rw [← hlower_add]
    exact lt_add_of_pos_left epsilon hlower
  have hsmall : Subsingleton ℝ ∨
      epsilon < ‖((ContinuousLinearEquiv.refl ℝ ℝ).symm : ℝ →L[ℝ] ℝ)‖₊⁻¹ := by
    right
    simpa only [ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.coe_refl,
      ContinuousLinearMap.nnnorm_id, inv_one] using hepsilon
  exact (antilipschitzWith_centerProjection R hR zeta hslope lower hlower hlower_add).to_rightInverse
    (Function.rightInverse_invFun (happrox.surjective hsmall))

/-- Inverse center parameters for two small graphs differ by at most the
remainder rate times their uniform distance and the inverse lower bound. -/
theorem dist_invFun_centerProjection_le
    (R : ℝ × X → ℝ × X) (hR : LipschitzWith epsilon R)
    (zeta eta : SmallLipschitzGraph X radius slope) (hslope : slope ≤ 1)
    (lower : ℝ≥0) (hlower : 0 < lower) (hlower_add : lower + epsilon = 1)
    (ubar : ℝ) :
    dist
        (Function.invFun (fun u : ℝ ↦ u + (R (u, zeta u)).1) ubar)
        (Function.invFun (fun u : ℝ ↦ u + (R (u, eta u)).1) ubar) ≤
      (lower⁻¹ : ℝ) * (epsilon : ℝ) * dist zeta eta := by
  -- Both center maps are surjective perturbations of the identity, hence their
  -- `invFun`s are genuine right inverses.
  have hepsilon : epsilon < 1 := by
    rw [← hlower_add]
    exact lt_add_of_pos_left epsilon hlower
  have hsmall : Subsingleton ℝ ∨
      epsilon < ‖((ContinuousLinearEquiv.refl ℝ ℝ).symm : ℝ →L[ℝ] ℝ)‖₊⁻¹ := by
    right
    simpa only [ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.coe_refl,
      ContinuousLinearMap.nnnorm_id, inv_one] using hepsilon
  have hzeta_surj := (centerProjection_approximatesId R hR zeta hslope).surjective hsmall
  have heta_surj := (centerProjection_approximatesId R hR eta hslope).surjective hsmall
  -- The common remainder is uniformly close along the two graph evaluations.
  have hcenter_bound (u : ℝ) :
      dist (u + (R (u, zeta u)).1) (u + (R (u, eta u)).1) ≤
        (epsilon : ℝ) * dist zeta eta := by
    calc
      dist (u + (R (u, zeta u)).1) (u + (R (u, eta u)).1) =
          dist ((R (u, zeta u)).1) ((R (u, eta u)).1) := by
            rw [dist_add_left]
      _ ≤ dist (R (u, zeta u)) (R (u, eta u)) := prod_fst_dist_le _ _
      _ ≤ (epsilon : ℝ) * dist (u, zeta u) (u, eta u) :=
        hR.dist_le_mul _ _
      _ = (epsilon : ℝ) * dist (zeta u) (eta u) := by
        rw [dist_prod_same_left]
      _ ≤ (epsilon : ℝ) * dist zeta eta :=
        mul_le_mul_of_nonneg_left (SmallLipschitzGraph.dist_apply_le zeta eta u)
          epsilon.coe_nonneg
  -- Apply the general stability estimate for right inverses and normalize the
  -- two nonnegative-real coercions.
  have hinverse := AntilipschitzWith.dist_rightInverse_rightInverse_le
    (antilipschitzWith_centerProjection R hR zeta hslope lower hlower hlower_add)
    (Function.rightInverse_invFun hzeta_surj) (Function.rightInverse_invFun heta_surj)
    hcenter_bound ubar
  simpa only [NNReal.coe_inv, mul_assoc] using hinverse

end LocalInvariantGraph

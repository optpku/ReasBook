module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.ConvexFunction
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.Problem
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Instances.EReal.Lemmas

@[expose] public section

open Filter

namespace ADMM.ConvergenceProof

/-- The coordinate dot product is continuous along two convergent sequences. -/
theorem tendsto_dotProduct {m : ℕ} {x y : ℕ → Fin m → ℝ}
    {xBar yBar : Fin m → ℝ} (hx : Tendsto x atTop (nhds xBar))
    (hy : Tendsto y atTop (nhds yBar)) :
    Tendsto (fun k ↦ dotProduct (x k) (y k)) atTop (nhds (dotProduct xBar yBar)) := by
  exact (continuous_fst.dotProduct continuous_snd).continuousAt.tendsto.comp
    (hx.prodMk_nhds hy)

/-- A supporting subgradient guarantees a finite objective value. -/
theorem subgradient_value_real {m : ℕ} {f : (Fin m → ℝ) → EReal}
    {x p : Fin m → ℝ} (h : IsSubgradientAt f p x) :
    f x = ((f x).toReal : EReal) := by
  obtain ⟨c, hc, _⟩ := h
  rw [hc, EReal.toReal_coe]

/-- At two graph points the extended-real support inequality has its usual
real-valued form, without requiring values outside the effective domain. -/
theorem subgradient_support_real {m : ℕ} {f : (Fin m → ℝ) → EReal}
    {x y p q : Fin m → ℝ} (hx : IsSubgradientAt f p x)
    (hy : IsSubgradientAt f q y) :
    (f x).toReal + dotProduct p (y - x) ≤ (f y).toReal := by
  obtain ⟨c, hc, hs⟩ := hx
  have h := hs y
  rw [hc, subgradient_value_real hy, ← EReal.coe_add, EReal.coe_le_coe_iff] at h
  simpa only [hc, EReal.toReal_coe] using h

/-- The graph of the subgradient relation is monotone. -/
theorem subgradient_monotone {m : ℕ} {f : (Fin m → ℝ) → EReal}
    {x y p q : Fin m → ℝ} (hx : IsSubgradientAt f p x)
    (hy : IsSubgradientAt f q y) :
    0 ≤ dotProduct (p - q) (x - y) := by
  have hxy := subgradient_support_real hx hy
  have hyx := subgradient_support_real hy hx
  simp only [sub_dotProduct, dotProduct_sub] at hxy hyx ⊢
  linarith

/-- Closedness of the epigraph passes convergent subgradient pairs to their
limit. The proof uses finite upper support planes, so it never assumes
continuity of the objective at a boundary point of its domain. -/
theorem subgradient_of_tendsto {m : ℕ} {f : (Fin m → ℝ) → EReal}
    (hf : IsClosedProperConvex f) {x p : ℕ → Fin m → ℝ} {xBar pBar : Fin m → ℝ}
    (hgraph : ∀ k, IsSubgradientAt f (p k) (x k))
    (hx : Tendsto x atTop (nhds xBar)) (hp : Tendsto p atTop (nhds pBar)) :
    IsSubgradientAt f pBar xBar := by
  -- For every fixed finite comparison point, the graph support planes bound
  -- the moving values from above by a convergent sequence of real heights.
  have hlimit (y : Fin m → ℝ) (c : ℝ) (hy : f y = (c : EReal)) :
      f xBar ≤ ((c - dotProduct pBar (y - xBar) : ℝ) : EReal) := by
    have hheight : Tendsto (fun k ↦ c - dotProduct (p k) (y - x k))
        atTop (nhds (c - dotProduct pBar (y - xBar))) :=
      tendsto_const_nhds.sub (tendsto_dotProduct hp (tendsto_const_nhds.sub hx))
    apply hf.epigraph_closed.mem_of_tendsto (hx.prodMk_nhds hheight)
    apply Eventually.of_forall
    intro k
    obtain ⟨ck, hck, hsupport⟩ := hgraph k
    have hineq := hsupport y
    rw [hck, hy, ← EReal.coe_add, EReal.coe_le_coe_iff] at hineq
    change f (x k) ≤ ((c - dotProduct (p k) (y - x k) : ℝ) : EReal)
    rw [hck, EReal.coe_le_coe_iff]
    linarith
  -- One finite comparison point rules out top at the limit.
  obtain ⟨y₀, hy₀⟩ := hf.exists_ne_top
  have hy₀real : f y₀ = ((f y₀).toReal : EReal) :=
    (EReal.coe_toReal hy₀ (hf.ne_bot y₀)).symm
  have hfinite : f xBar ≠ ⊤ :=
    ne_top_of_le_ne_top (EReal.coe_ne_top _) (hlimit y₀ (f y₀).toReal hy₀real)
  have hxreal : f xBar = ((f xBar).toReal : EReal) :=
    (EReal.coe_toReal hfinite (hf.ne_bot xBar)).symm
  refine ⟨(f xBar).toReal, hxreal, ?_⟩
  intro y
  by_cases hy : f y = ⊤
  · rw [hy]
    exact le_top
  · have hyreal : f y = ((f y).toReal : EReal) :=
      (EReal.coe_toReal hy (hf.ne_bot y)).symm
    have hineq := hlimit y (f y).toReal hyreal
    rw [hxreal, EReal.coe_le_coe_iff] at hineq
    rw [hxreal, hyreal, ← EReal.coe_add, EReal.coe_le_coe_iff]
    linarith

/-- Objective values converge along a convergent subgradient graph sequence.
Two support planes squeeze the values, which avoids a false global continuity
assumption for extended-real convex functions. -/
theorem subgradient_value_tendsto {m : ℕ} {f : (Fin m → ℝ) → EReal}
    {x p : ℕ → Fin m → ℝ} {xBar pBar : Fin m → ℝ}
    (hgraph : ∀ k, IsSubgradientAt f (p k) (x k))
    (hlimit : IsSubgradientAt f pBar xBar)
    (hx : Tendsto x atTop (nhds xBar)) (hp : Tendsto p atTop (nhds pBar)) :
    Tendsto (fun k ↦ (f (x k)).toReal) atTop (nhds (f xBar).toReal) := by
  have hlower : ∀ k, (f xBar).toReal + dotProduct pBar (x k - xBar) ≤
      (f (x k)).toReal := fun k ↦ subgradient_support_real hlimit (hgraph k)
  have hupper : ∀ k, (f (x k)).toReal ≤
      (f xBar).toReal - dotProduct (p k) (xBar - x k) := by
    intro k
    linarith [subgradient_support_real (hgraph k) hlimit]
  have hc : Tendsto (fun _ : ℕ ↦ (f xBar).toReal) atTop (nhds (f xBar).toReal) :=
    tendsto_const_nhds
  have hxc : Tendsto (fun _ : ℕ ↦ xBar) atTop (nhds xBar) := tendsto_const_nhds
  have hpc : Tendsto (fun _ : ℕ ↦ pBar) atTop (nhds pBar) := tendsto_const_nhds
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le _ _ hlower hupper
  · simpa only [sub_self, dotProduct_zero, add_zero] using
      hc.add (tendsto_dotProduct hpc (hx.sub hxc))
  · simpa only [sub_self, dotProduct_zero, sub_zero] using
      hc.sub (tendsto_dotProduct hp (hxc.sub hx))

/-- The same graph convergence gives convergence in the extended-real topology. -/
theorem subgradient_ereal_value_tendsto {m : ℕ} {f : (Fin m → ℝ) → EReal}
    {x p : ℕ → Fin m → ℝ} {xBar pBar : Fin m → ℝ}
    (hgraph : ∀ k, IsSubgradientAt f (p k) (x k))
    (hlimit : IsSubgradientAt f pBar xBar)
    (hx : Tendsto x atTop (nhds xBar)) (hp : Tendsto p atTop (nhds pBar)) :
    Tendsto (fun k ↦ f (x k)) atTop (nhds (f xBar)) := by
  have h := continuous_coe_real_ereal.continuousAt.tendsto.comp
    (subgradient_value_tendsto hgraph hlimit hx hp)
  simpa only [Function.comp_def, ← subgradient_value_real (hgraph _),
    ← subgradient_value_real hlimit] using h

end ADMM.ConvergenceProof

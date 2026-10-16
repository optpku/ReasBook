module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.ImageReduction
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.Optimality
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.Convergence.ProofSupport.ReducedOrbitLimit
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

open Filter

namespace ADMM.ConvergenceProof

/-- The biconjugate lies below any finite upper bound for the original value. -/
lemma biconjugate_le_of_le {m : ℕ} {φ : (Fin m → ℝ) → EReal}
    {x : Fin m → ℝ} {c : ℝ} (h : φ x ≤ (c : EReal)) :
    ERealConvex.fenchelBiconjugate φ x ≤ (c : EReal) := by
  rw [ERealConvex.fenchelBiconjugate_apply, ERealConvex.fenchelConjugate_apply]
  apply sSup_le
  rintro r ⟨p, rfl⟩
  have hlower : ((dotProduct x p : ℝ) : EReal) - (c : EReal) ≤
      ERealConvex.fenchelConjugate φ p := by
    apply (EReal.sub_le_sub le_rfl h).trans
    rw [ERealConvex.fenchelConjugate_apply]
    exact le_sSup ⟨x, rfl⟩
  have hsum := (EReal.sub_le_iff_le_add (.inl (EReal.coe_ne_bot c))
    (.inl (EReal.coe_ne_top c))).mp hlower
  rw [dotProduct_comm p x]
  exact EReal.sub_le_of_le_add' hsum

/-- Every reduced image value is bounded by the corresponding original value,
including at original points outside the effective domain. -/
lemma reduced_first_le {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m)
    (hf : IsClosedProperConvex P.f) {β : ℝ} (hβ : 0 < β) (x : Fin n₁ → ℝ) :
    (P.reduced β).f (P.A.mulVec x) ≤ P.f x / (β : EReal) := by
  rw [Problem.reduced_f, ImageReduction.reducedFirst_apply]
  apply EReal.div_le_div_right_of_nonneg (EReal.coe_nonneg.mpr hβ.le)
  by_cases hx : P.f x = ⊤
  · simp [hx]
  · rw [← EReal.coe_toReal hx (hf.ne_bot x)]
    apply biconjugate_le_of_le
    rw [EReal.coe_toReal hx (hf.ne_bot x)]
    exact ImageReduction.fiberInf_le_of_mulVec_eq P.f P.A rfl

lemma reduced_second_le {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m)
    (hg : IsClosedProperConvex P.g) {β : ℝ} (hβ : 0 < β) (y : Fin n₂ → ℝ) :
    (P.reduced β).g (P.B.mulVec y - P.b) ≤ P.g y / (β : EReal) := by
  rw [Problem.reduced_g, ImageReduction.reducedSecond_apply]
  apply EReal.div_le_div_right_of_nonneg (EReal.coe_nonneg.mpr hβ.le)
  by_cases hy : P.g y = ⊤
  · simp [hy]
  · rw [← EReal.coe_toReal hy (hg.ne_bot y)]
    apply biconjugate_le_of_le
    rw [EReal.coe_toReal hy (hg.ne_bot y), ImageReduction.shiftedFiberInf_apply]
    exact sInf_le ⟨y, rfl, rfl⟩

/-- A supporting plane for a scaled image objective lifts through its matrix
when the reduced and original values agree at the selected point. -/
lemma subgradient_pullback_scaled {n m : ℕ} {φ : (Fin n → ℝ) → EReal}
    {ψ : (Fin m → ℝ) → EReal} (L : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) {β : ℝ} (hβ : 0 < β) {p : Fin m → ℝ} {x : Fin n → ℝ}
    (hlower : ∀ z, ψ (L.mulVec z - b) ≤ φ z / (β : EReal))
    (hvalue : ψ (L.mulVec x - b) = φ x / (β : EReal))
    (hsub : IsSubgradientAt ψ p (L.mulVec x - b)) :
    IsSubgradientAt φ (L.transpose.mulVec (β • p)) x := by
  obtain ⟨c, hc, hs⟩ := hsub
  have hφx : φ x = ((c * β : ℝ) : EReal) := by
    have h := congrArg (fun a : EReal ↦ a * (β : EReal)) (hc.symm.trans hvalue)
    simpa only [← EReal.coe_mul, EReal.div_mul_cancel (EReal.coe_ne_bot β)
      (EReal.coe_ne_top β) (EReal.coe_ne_zero.mpr hβ.ne')] using h.symm
  refine ⟨c * β, hφx, ?_⟩
  intro z
  have h := (hs (L.mulVec z - b)).trans (hlower z)
  rw [hc, ← EReal.coe_add] at h
  have hmul := (EReal.le_div_iff_mul_le (EReal.coe_pos.mpr hβ) (EReal.coe_ne_top β)).mp h
  rw [← EReal.coe_mul] at hmul
  rw [hφx, ← EReal.coe_add]
  convert hmul using 1
  congr 1
  have hdot : dotProduct (L.transpose.mulVec (β • p)) (z - x) =
      β * dotProduct p ((L.mulVec z - b) - (L.mulVec x - b)) := by
    rw [dotProduct_comm, Matrix.dotProduct_transpose_mulVec,
      smul_dotProduct, smul_eq_mul, Matrix.mulVec_sub, sub_sub_sub_cancel_right]
  rw [hdot]
  ring

/-- Two KKT pairs of a consensus problem can exchange multipliers: all primal
solutions share every optimal supporting multiplier. -/
lemma consensus_mix_subgradients {m : ℕ} {f g : (Fin m → ℝ) → EReal}
    {q v u q' v' u' : Fin m → ℝ}
    (hfeas : q + v = 0) (hfeas' : q' + v' = 0)
    (hf : IsSubgradientAt f (-u) q) (hg : IsSubgradientAt g (-u) v)
    (hf' : IsSubgradientAt f (-u') q') (hg' : IsSubgradientAt g (-u') v') :
    IsSubgradientAt f (-u') q ∧ IsSubgradientAt g (-u') v := by
  have hfirst := subgradient_support_real hf hf'
  have hsecond := subgradient_support_real hg hg'
  have hfirst' := subgradient_support_real hf' hf
  have hsecond' := subgradient_support_real hg' hg
  have hdiff : (q' - q) + (v' - v) = 0 := by
    calc
      (q' - q) + (v' - v) = (q' + v') - (q + v) := by abel
      _ = 0 := by rw [hfeas, hfeas', sub_self]
  have hdot (p : Fin m → ℝ) : dotProduct p (q' - q) + dotProduct p (v' - v) = 0 := by
    rw [← dotProduct_add, hdiff, dotProduct_zero]
  have hsum : (f q).toReal + (g v).toReal = (f q').toReal + (g v').toReal := by
    have hu := hdot (-u)
    have hu' := hdot (-u')
    simp only [dotProduct_sub] at hu hu' hfirst hsecond hfirst' hsecond'
    linarith
  have heqf : (f q).toReal = (f q').toReal + dotProduct (-u') (q - q') := by
    have hu' := hdot (-u')
    simp only [dotProduct_sub] at hu' hfirst' hsecond' ⊢
    linarith
  have heqg : (g v).toReal = (g v').toReal + dotProduct (-u') (v - v') := by
    have hu' := hdot (-u')
    simp only [dotProduct_sub] at hu' hfirst' hsecond' ⊢
    linarith
  have transfer {φ : (Fin m → ℝ) → EReal} {a a' p : Fin m → ℝ}
      (ha : ∃ c : ℝ, φ a = c) (ha' : IsSubgradientAt φ p a')
      (heq : (φ a).toReal = (φ a').toReal + dotProduct p (a - a')) :
      IsSubgradientAt φ p a := by
    obtain ⟨c, hc⟩ := ha
    have hval := subgradient_value_real ha'
    obtain ⟨c', hc', hs'⟩ := ha'
    refine ⟨c, hc, ?_⟩
    intro z
    have h := hs' z
    rw [hval, ← EReal.coe_add] at h
    rw [hc, ← EReal.coe_add]
    convert h using 1
    congr 1
    rw [hc, EReal.toReal_coe, dotProduct_sub] at heq
    simp only [dotProduct_sub]
    linarith
  obtain ⟨cf, hcf, _⟩ := hf
  obtain ⟨cg, hcg, _⟩ := hg
  exact ⟨transfer ⟨cf, hcf⟩ hf' heqf, transfer ⟨cg, hcg⟩ hg' heqg⟩

/-- A reduced KKT multiplier lifts to an optimal original multiplier by pairing
it with the already available original primal KKT solution. -/
theorem reduced_optimalMultiplier {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m)
    (hf : IsClosedProperConvex P.f) (hg : IsClosedProperConvex P.g)
    (hKKT : ∃ x y multiplier, P.IsKKT x y multiplier) {β : ℝ} (hβ : 0 < β)
    {q v u : Fin m → ℝ} (hred : (P.reduced β).IsKKT q v u) :
    P.IsOptimalMultiplier (β • u) := by
  obtain ⟨x, y, multiplier, hkkt⟩ := hKKT
  have hb := hkkt.reducedBundle hβ
  have hmix := consensus_mix_subgradients
    (by simpa [Problem.reduced_A, Problem.reduced_B, Problem.reduced_b] using hb.1.feasible)
    (by simpa [Problem.reduced_A, Problem.reduced_B, Problem.reduced_b] using hred.feasible)
    (by simpa [Problem.reduced_A] using hb.1.firstStationary)
    (by simpa [Problem.reduced_B] using hb.1.secondStationary)
    (by simpa [Problem.reduced_A] using hred.firstStationary)
    (by simpa [Problem.reduced_B] using hred.secondStationary)
  refine ⟨x, y, ?_, ?_, hkkt.feasible⟩
  · have hp := subgradient_pullback_scaled P.A 0 hβ
      (fun z ↦ by simpa using reduced_first_le P hf hβ z)
      (by simpa using hb.2.2.2.1) (by simpa using hmix.1)
    simpa [smul_neg, Matrix.mulVec_neg] using hp
  · have hp := subgradient_pullback_scaled P.B P.b hβ
      (reduced_second_le P hg hβ) hb.2.2.2.2.1 hmix.2
    simpa [smul_neg, Matrix.mulVec_neg] using hp

/-- The unscaled trajectory updates have original-space subgradients. -/
lemma original_graph_laws {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m)
    (hf : IsClosedProperConvex P.f) (hg : IsClosedProperConvex P.g)
    {β γ : ℝ} (hβ : 0 < β) (z : Trajectory P β γ) (k : ℕ) :
    IsSubgradientAt P.f
      (-P.A.transpose.mulVec (z.multiplier k + β •
        (P.A.mulVec (z.x (k + 1)) + (P.B.mulVec (z.y k) - P.b)))) (z.x (k + 1)) ∧
    IsSubgradientAt P.g
      (-P.B.transpose.mulVec (z.multiplier k + β •
        (P.A.mulVec (z.x (k + 1)) + (P.B.mulVec (z.y (k + 1)) - P.b)))) (z.y (k + 1)) := by
  constructor
  · apply isSubgradientAtOfAugmentedMinimizer hf P.A _ _ hβ
    have h := z.firstMinimizes k
    change IsFiniteMinimizer (fun x ↦ P.f x +
      dotProduct (z.multiplier k) (P.A.mulVec x + P.B.mulVec (z.y k) - P.b) +
      (((β / 2) * dotProduct (P.A.mulVec x + P.B.mulVec (z.y k) - P.b)
        (P.A.mulVec x + P.B.mulVec (z.y k) - P.b) : ℝ) : EReal)) (z.x (k + 1)) at h
    simpa only [add_sub_assoc] using h
  · have hfun : (fun y ↦ P.g y +
        dotProduct (z.multiplier k) (P.B.mulVec y + (P.A.mulVec (z.x (k + 1)) - P.b)) +
        (((β / 2) * dotProduct (P.B.mulVec y + (P.A.mulVec (z.x (k + 1)) - P.b))
          (P.B.mulVec y + (P.A.mulVec (z.x (k + 1)) - P.b)) : ℝ) : EReal)) =
      P.secondBlockObjective β (z.multiplier k) (z.x (k + 1)) := by
      funext y
      have hres : P.B.mulVec y + (P.A.mulVec (z.x (k + 1)) - P.b) =
          P.A.mulVec (z.x (k + 1)) + P.B.mulVec y - P.b := by abel
      simp only [Problem.secondBlockObjective, hres]
    have h := isSubgradientAtOfAugmentedMinimizer hg P.B
      (P.A.mulVec (z.x (k + 1)) - P.b) (z.multiplier k) hβ (z.y (k + 1))
      (by rw [hfun]; exact z.secondMinimizes k)
    have hres : P.B.mulVec (z.y (k + 1)) + (P.A.mulVec (z.x (k + 1)) - P.b) =
        P.A.mulVec (z.x (k + 1)) + (P.B.mulVec (z.y (k + 1)) - P.b) := by abel
    rwa [hres] at h

/-- Injectivity of a finite-dimensional matrix map reflects convergence to a
specified compatible preimage. -/
lemma tendsto_of_image {n m : ℕ} (L : Matrix (Fin m) (Fin n) ℝ)
    (hL : Function.Injective L.mulVec) {s : ℕ → Fin n → ℝ} {x : Fin n → ℝ}
    (h : Tendsto (fun k ↦ L.mulVec (s k)) atTop (nhds (L.mulVec x))) :
    Tendsto s atTop (nhds x) := by
  have hker : LinearMap.ker L.mulVecLin = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    simpa only [Matrix.coe_mulVecLin] using hL
  have hc := LinearMap.isClosedEmbedding_of_injective hker
  exact hc.tendsto_nhds_iff.mpr h

/-- With injective primal maps, compatible image limits yield the original KKT
triple through closedness of the original subgradient graphs. -/
lemma original_kkt_of_limits {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m)
    (hf : IsClosedProperConvex P.f) (hg : IsClosedProperConvex P.g)
    {β γ : ℝ} (hβ : 0 < β) (z : Trajectory P β γ)
    {q v u : Fin m → ℝ} (hfeas : q + v = 0)
    (hq : Tendsto (fun k ↦ P.A.mulVec (z.x k)) atTop (nhds q))
    (hv : Tendsto (fun k ↦ P.B.mulVec (z.y k) - P.b) atTop (nhds v))
    (hu : Tendsto (fun k ↦ β⁻¹ • z.multiplier k) atTop (nhds u))
    (hA : Function.Injective P.A.mulVec) (hB : Function.Injective P.B.mulVec)
    (x : Fin n₁ → ℝ) (y : Fin n₂ → ℝ)
    (hx : P.A.mulVec x = q) (hy : P.B.mulVec y - P.b = v) :
    P.IsKKT x y (β • u) := by
  have hxs : Tendsto (fun k ↦ z.x (k + 1)) atTop (nhds x) :=
    (tendsto_of_image P.A hA (by rwa [hx])).comp (tendsto_add_atTop_nat 1)
  have hys : Tendsto (fun k ↦ z.y (k + 1)) atTop (nhds y) := by
    apply (tendsto_of_image P.B hB ?_).comp (tendsto_add_atTop_nat 1)
    have h := hv.add_const P.b
    simpa only [← hy, sub_add_cancel] using h
  have hum : Tendsto z.multiplier atTop (nhds (β • u)) := by
    simpa only [smul_smul, mul_inv_cancel₀ hβ.ne', one_smul] using hu.const_smul β
  have hqs := hq.comp (tendsto_add_atTop_nat 1)
  have hvs := hv.comp (tendsto_add_atTop_nat 1)
  have hAc : Continuous (fun a : Fin m → ℝ ↦ P.A.transpose.mulVec a) :=
    continuous_const.matrix_mulVec continuous_id
  have hBc : Continuous (fun a : Fin m → ℝ ↦ P.B.transpose.mulVec a) :=
    continuous_const.matrix_mulVec continuous_id
  have hnormalF := hAc.continuousAt.tendsto.comp (hum.add ((hqs.add hv).const_smul β))
  have hnormalG := hBc.continuousAt.tendsto.comp (hum.add ((hqs.add hvs).const_smul β))
  have hfirst := subgradient_of_tendsto hf (fun k ↦ (original_graph_laws P hf hg hβ z k).1)
    hxs (by simpa only [Function.comp_apply, hfeas, smul_zero, add_zero] using hnormalF.neg)
  have hsecond := subgradient_of_tendsto hg (fun k ↦ (original_graph_laws P hf hg hβ z k).2)
    hys (by simpa only [Function.comp_apply, hfeas, smul_zero, add_zero] using hnormalG.neg)
  refine ⟨hfirst, hsecond, ?_⟩
  have h : P.A.mulVec x + (P.B.mulVec y - P.b) = 0 := by rw [hx, hy, hfeas]
  exact sub_eq_zero.mp (by simpa only [← add_sub_assoc] using h)

/-- Transport the convergent reduced orbit and its finite objective limits to
all original-space conclusions used by the public convergence bundle. -/
theorem reducedOrbitConclusions_from_limits {n₁ n₂ m : ℕ} (P : Problem n₁ n₂ m)
    (hf : IsClosedProperConvex P.f) (hg : IsClosedProperConvex P.g)
    (hKKT : ∃ x y multiplier, P.IsKKT x y multiplier) {β γ : ℝ}
    (hβ : 0 < β) (hγ : 0 < γ) (z : Trajectory P β γ)
    {q v u : Fin m → ℝ}
    (hq : Tendsto (fun k ↦ P.A.mulVec (z.x k)) atTop (nhds q))
    (hv : Tendsto (fun k ↦ P.B.mulVec (z.y k) - P.b) atTop (nhds v))
    (hu : Tendsto (fun k ↦ β⁻¹ • z.multiplier k) atTop (nhds u))
    (hred : (P.reduced β).IsKKT q v u)
    (hF : Tendsto (fun k ↦ (P.reduced β).f (P.A.mulVec (z.x k))) atTop
      (nhds ((P.reduced β).f q)))
    (hG : Tendsto (fun k ↦ (P.reduced β).g (P.B.mulVec (z.y k) - P.b)) atTop
      (nhds ((P.reduced β).g v))) :
    Tendsto (fun k ↦ P.A.mulVec (z.x k) + (P.B.mulVec (z.y k) - P.b)) atTop (nhds 0) ∧
    Tendsto (fun k ↦ (P.B.mulVec (z.y k) - P.b) -
      (P.B.mulVec (z.y (k - 1)) - P.b)) atTop (nhds 0) ∧
    Tendsto (fun k ↦ P.objective (z.x k) (z.y k) / (β : EReal)) atTop
      (nhds (P.optimalValue / (β : EReal))) ∧
    P.IsOptimalMultiplier (β • u) ∧
    ∀ _ : Function.Injective P.A.mulVec, Function.Injective P.B.mulVec →
      ∀ x y, P.A.mulVec x = q → P.B.mulVec y - P.b = v → P.IsKKT x y (β • u) := by
  have hfeas : q + v = 0 := by
    simpa [Problem.reduced_A, Problem.reduced_B, Problem.reduced_b] using hred.feasible
  have hres : Tendsto (fun k ↦ P.A.mulVec (z.x k) + (P.B.mulVec (z.y k) - P.b))
      atTop (nhds 0) := by simpa only [hfeas] using hq.add hv
  have hinc : Tendsto (fun k ↦ (P.B.mulVec (z.y k) - P.b) -
      (P.B.mulVec (z.y (k - 1)) - P.b)) atTop (nhds 0) := by
    simpa only [sub_self, Function.comp_apply] using hv.sub (hv.comp (tendsto_sub_atTop_nat 1))
  have hopt := reduced_optimalMultiplier P hf hg hKKT hβ hred
  refine ⟨hres, hinc, ?_, hopt, original_kkt_of_limits P hf hg hβ z hfeas hq hv hu⟩
  obtain ⟨cf, hcf, _⟩ := hred.firstStationary
  obtain ⟨cg, hcg, _⟩ := hred.secondStationary
  have hsum : Tendsto (fun k ↦ (P.reduced β).f (P.A.mulVec (z.x k)) +
      (P.reduced β).g (P.B.mulVec (z.y k) - P.b)) atTop
      (nhds ((P.reduced β).f q + (P.reduced β).g v)) := by
    rw [hcf] at hF
    rw [hcg] at hG
    rw [hcf, hcg]
    exact (EReal.continuousAt_add_coe_coe cf cg).tendsto.comp (hF.prodMk_nhds hG)
  have hsumValue : (P.reduced β).f q + (P.reduced β).g v = P.optimalValue / (β : EReal) := by
    rw [← Problem.objective_apply, ← hred.optimalValue_eq_objective]
    exact Problem.reduced_optimalValue P hf hg hKKT hβ hγ z
  rw [hsumValue] at hsum
  apply (tendsto_add_atTop_iff_nat 1).mp
  apply (hsum.comp (tendsto_add_atTop_nat 1)).congr
  intro k
  have hfirst := (Trajectory.firstImage_values P hf hg hKKT hβ hγ z k).2
  have hsecond := (Trajectory.secondImage_values P hf hg hKKT hβ hγ z k).2
  obtain ⟨a, ha, _⟩ := (original_graph_laws P hf hg hβ z k).1
  obtain ⟨b, hb, _⟩ := (original_graph_laws P hf hg hβ z k).2
  simp only [Function.comp_apply, Problem.reduced_f, Problem.reduced_g,
    ImageReduction.reducedFirst_apply, ImageReduction.reducedSecond_apply,
    hfirst, hsecond, Problem.objective_apply, ha, hb, ← EReal.coe_add, ← EReal.coe_div]
  congr 1
  ring

end ADMM.ConvergenceProof

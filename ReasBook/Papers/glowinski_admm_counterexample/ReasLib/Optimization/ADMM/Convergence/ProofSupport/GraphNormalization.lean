module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.Convergence.ProofSupport.GraphLimits

@[expose] public section

namespace ADMM.ConvergenceProof

/-- Translate the origin to a finite graph point and subtract its supporting
plane. The affine term is real even when the evaluated objective is infinite. -/
noncomputable def normalizedObjective {m : ℕ} (f : (Fin m → ℝ) → EReal)
    (xStar pStar : Fin m → ℝ) (x : Fin m → ℝ) : EReal :=
  f (x + xStar) + ((-(f xStar).toReal - dotProduct pStar x : ℝ) : EReal)

/-- Translation and affine tilt preserve supporting subgradients, with their
positions and normals translated by the chosen graph point. -/
theorem subgradient_normalized {m : ℕ} {f : (Fin m → ℝ) → EReal}
    (hf : IsClosedProperConvex f) (xStar pStar : Fin m → ℝ)
    {x p : Fin m → ℝ} (hx : IsSubgradientAt f p x) :
    IsSubgradientAt (normalizedObjective f xStar pStar) (p - pStar) (x - xStar) := by
  obtain ⟨cx, hcx, hs⟩ := hx
  have hvalue : normalizedObjective f xStar pStar (x - xStar) =
      ((cx - (f xStar).toReal - dotProduct pStar (x - xStar) : ℝ) : EReal) := by
    simp only [normalizedObjective, sub_add_cancel, hcx, ← EReal.coe_add]
    congr 1
    ring
  refine ⟨cx - (f xStar).toReal - dotProduct pStar (x - xStar), hvalue, ?_⟩
  intro y
  by_cases hy : f (y + xStar) = ⊤
  · simp only [normalizedObjective, hy, EReal.top_add_coe, le_top]
  · have hyreal : f (y + xStar) = ((f (y + xStar)).toReal : EReal) :=
      (EReal.coe_toReal hy (hf.ne_bot _)).symm
    have h := hs (y + xStar)
    rw [hcx, hyreal, ← EReal.coe_add, EReal.coe_le_coe_iff] at h
    rw [hvalue, normalizedObjective, hyreal, ← EReal.coe_add, ← EReal.coe_add,
      EReal.coe_le_coe_iff]
    simp only [sub_dotProduct, dotProduct_add, dotProduct_sub] at h ⊢
    linarith

/-- The chosen KKT supporting plane becomes the zero subgradient at the origin. -/
theorem subgradient_normalized_zero {m : ℕ} {f : (Fin m → ℝ) → EReal}
    (hf : IsClosedProperConvex f) {xStar pStar : Fin m → ℝ}
    (hStar : IsSubgradientAt f pStar xStar) :
    IsSubgradientAt (normalizedObjective f xStar pStar) 0 0 := by
  simpa only [sub_self] using subgradient_normalized hf xStar pStar hStar

/-- Reflection of a convex graph negates both its position and normal. -/
theorem subgradient_reflected {m : ℕ} {f : (Fin m → ℝ) → EReal}
    {x p : Fin m → ℝ} (hx : IsSubgradientAt f p x) :
    IsSubgradientAt (fun y ↦ f (-y)) (-p) (-x) := by
  obtain ⟨c, hc, hs⟩ := hx
  refine ⟨c, by simpa only [neg_neg] using hc, ?_⟩
  intro y
  have h := hs (-y)
  have hdot : dotProduct (-p) (y - -x) = dotProduct p (-y - x) := by
    simp only [neg_dotProduct, dotProduct_sub, dotProduct_neg]
    ring
  simpa only [neg_neg, hdot] using h

/-- Real epigraph heights of the normalized objective are affine pullbacks of
heights of the original objective. -/
theorem normalizedObjective_le_iff {m : ℕ} (f : (Fin m → ℝ) → EReal)
    (xStar pStar x : Fin m → ℝ) (t : ℝ) :
    normalizedObjective f xStar pStar x ≤ (t : EReal) ↔
      f (x + xStar) ≤ ((t + (f xStar).toReal + dotProduct pStar x : ℝ) : EReal) := by
  rw [normalizedObjective, ← EReal.le_sub_iff_add_le
    (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _)), ← EReal.coe_sub]
  have heq : t - (-(f xStar).toReal - dotProduct pStar x) =
      t + (f xStar).toReal + dotProduct pStar x := by ring
  rw [heq]

/-- Translation and subtraction of a finite supporting plane preserve closed
proper convexity. -/
theorem normalizedObjective_closedProperConvex {m : ℕ} {f : (Fin m → ℝ) → EReal}
    (hf : IsClosedProperConvex f) {xStar pStar : Fin m → ℝ}
    (hStar : IsSubgradientAt f pStar xStar) :
    IsClosedProperConvex (normalizedObjective f xStar pStar) := by
  refine IsClosedProperConvex.ofEpigraph ?_ ?_ ?_ ?_
  · rw [convex_iff_add_mem]
    intro u hu v hv s t hs ht hst
    have hu' := (normalizedObjective_le_iff f xStar pStar u.1 u.2).1 hu
    have hv' := (normalizedObjective_le_iff f xStar pStar v.1 v.2).1 hv
    have huE : (u.1 + xStar, u.2 + (f xStar).toReal + dotProduct pStar u.1) ∈
        {z : (Fin m → ℝ) × ℝ | f z.1 ≤ (z.2 : EReal)} := hu'
    have hvE : (v.1 + xStar, v.2 + (f xStar).toReal + dotProduct pStar v.1) ∈
        {z : (Fin m → ℝ) × ℝ | f z.1 ≤ (z.2 : EReal)} := hv'
    have h := hf.epigraph_convex huE hvE hs ht hst
    apply (normalizedObjective_le_iff f xStar pStar _ _).2
    change f (s • (u.1 + xStar) + t • (v.1 + xStar)) ≤
      ((s * (u.2 + (f xStar).toReal + dotProduct pStar u.1) +
        t * (v.2 + (f xStar).toReal + dotProduct pStar v.1) : ℝ) : EReal) at h
    have hx : s • (u.1 + xStar) + t • (v.1 + xStar) =
        (s • u.1 + t • v.1) + xStar := by
      calc
        _ = s • u.1 + t • v.1 + (s + t) • xStar := by module
        _ = _ := by rw [hst, one_smul]
    have ht' : s * (u.2 + (f xStar).toReal + dotProduct pStar u.1) +
        t * (v.2 + (f xStar).toReal + dotProduct pStar v.1) =
        (s * u.2 + t * v.2) + (f xStar).toReal +
          dotProduct pStar (s • u.1 + t • v.1) := by
      simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
      nlinarith [congrArg (fun a : ℝ ↦ a * (f xStar).toReal) hst]
    rw [hx, ht'] at h
    exact h
  · have hepi : {z : (Fin m → ℝ) × ℝ |
        normalizedObjective f xStar pStar z.1 ≤ (z.2 : EReal)} =
        (fun z : (Fin m → ℝ) × ℝ ↦
          (z.1 + xStar, z.2 + (f xStar).toReal + dotProduct pStar z.1)) ⁻¹'
          {z : (Fin m → ℝ) × ℝ | f z.1 ≤ (z.2 : EReal)} := by
      ext z
      exact normalizedObjective_le_iff f xStar pStar z.1 z.2
    rw [hepi]
    exact hf.epigraph_closed.preimage ((continuous_fst.add continuous_const).prodMk
      ((continuous_snd.add continuous_const).add (continuous_const.dotProduct continuous_fst)))
  · intro x
    exact EReal.add_ne_bot_iff.mpr ⟨hf.ne_bot _, EReal.coe_ne_bot _⟩
  · obtain ⟨c, hc, _⟩ := subgradient_normalized_zero hf hStar
    exact ⟨0, by rw [hc]; exact EReal.coe_ne_top c⟩

/-- Reflection of the argument preserves closed proper convexity. -/
theorem reflectedObjective_closedProperConvex {m : ℕ} {f : (Fin m → ℝ) → EReal}
    (hf : IsClosedProperConvex f) : IsClosedProperConvex (fun x ↦ f (-x)) := by
  refine IsClosedProperConvex.ofEpigraph ?_ ?_ ?_ ?_
  · rw [convex_iff_add_mem]
    intro u hu v hv s t hs ht hst
    have huE : (-u.1, u.2) ∈ {z : (Fin m → ℝ) × ℝ | f z.1 ≤ (z.2 : EReal)} := hu
    have hvE : (-v.1, v.2) ∈ {z : (Fin m → ℝ) × ℝ | f z.1 ≤ (z.2 : EReal)} := hv
    have h := hf.epigraph_convex huE hvE hs ht hst
    change f (s • -u.1 + t • -v.1) ≤ ((s * u.2 + t * v.2 : ℝ) : EReal) at h
    change f (-(s • u.1 + t • v.1)) ≤ ((s * u.2 + t * v.2 : ℝ) : EReal)
    simpa only [smul_neg, neg_add] using h
  · exact hf.epigraph_closed.preimage (continuous_fst.neg.prodMk continuous_snd)
  · exact fun x ↦ hf.ne_bot (-x)
  · obtain ⟨x, hx⟩ := hf.exists_ne_top
    exact ⟨-x, by simpa only [neg_neg] using hx⟩

end ADMM.ConvergenceProof

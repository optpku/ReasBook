module

public import ReasLib.Analysis.Calculus.ContDiff.DisjointFinsumC2
public import ReasLib.Analysis.Calculus.ContDiff.ZeroExtensionJets.EqOn

public section

open Filter Set Topology

universe u v

variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A disjoint shrinking family with supportwise value, first-derivative, and second-derivative
decay yields a global C² zero extension together with its value and first two Fréchet jets
vanishing on the closed cluster set. -/
theorem contDiff_two_indicator_compl_finsum_eqOn_zero_jets
    (Γ : Set E) (x : ℕ → E) (ρ : ℕ → ℝ) (ψ : ℕ → E → F) (hΓ : IsClosed Γ)
    (hcluster : ∀ y, MapClusterPt y atTop x → y ∈ Γ) (hρ : ∀ k, 0 ≤ ρ k)
    (hρ0 : Tendsto ρ atTop (𝓝 0))
    (hballs : Set.univ.PairwiseDisjoint (fun k ↦ Metric.closedBall (x k) (ρ k)))
    (hsupport : ∀ k, tsupport (ψ k) ⊆ Metric.closedBall (x k) (ρ k))
    (hsmooth : ∀ k, ContDiff ℝ 2 (ψ k))
    (hvalueDecay : ∀ η > 0, ∃ δ > 0, ∀ k z,
      z ∈ Γᶜ → z ∈ tsupport (ψ k) → Metric.infDist z Γ < δ →
        ‖ψ k z‖ / Metric.infDist z Γ ^ 2 < η)
    (hderivDecay : ∀ η > 0, ∃ δ > 0, ∀ k z,
      z ∈ Γᶜ → z ∈ tsupport (ψ k) → Metric.infDist z Γ < δ →
        ‖fderiv ℝ (ψ k) z‖ / Metric.infDist z Γ < η)
    (hsecondDecay : ∀ η > 0, ∃ δ > 0, ∀ k z,
      z ∈ Γᶜ → z ∈ tsupport (ψ k) → Metric.infDist z Γ < δ →
        ‖fderiv ℝ (fderiv ℝ (ψ k)) z‖ < η) :
    ContDiff ℝ 2 (Γᶜ.indicator fun z ↦ ∑ᶠ k, ψ k z) ∧
      EqOn (Γᶜ.indicator (fun z ↦ ∑ᶠ k, ψ k z)) 0 Γ ∧
      EqOn (fderiv ℝ (Γᶜ.indicator (fun z ↦ ∑ᶠ k, ψ k z))) 0 Γ ∧
      EqOn (fderiv ℝ (fderiv ℝ (Γᶜ.indicator (fun z ↦ ∑ᶠ k, ψ k z)))) 0 Γ := by
  have hcont := contDiff_two_indicator_compl_finsum_of_supportwise_decay Γ x ρ ψ hΓ
    hcluster hρ hρ0 hballs hsupport hsmooth hvalueDecay hderivDecay hsecondDecay
  have hj0 : 0 ≤ 2 := Nat.zero_le 2
  have hj1 : 1 ≤ 2 := by omega
  have hdecay0 : ∀ η > 0, ∃ δ > 0, ∀ k z,
      z ∈ Γᶜ → z ∈ tsupport (ψ k) → Metric.infDist z Γ < δ →
        ‖iteratedFDeriv ℝ 0 (ψ k) z‖ / Metric.infDist z Γ ^ 2 < η := by
    intro η hη
    obtain ⟨δ, hδ, hbound⟩ := hvalueDecay η hη
    refine ⟨δ, hδ, ?_⟩
    intro k z hzΓ hzk hzδ
    simpa only [norm_iteratedFDeriv_zero] using hbound k z hzΓ hzk hzδ
  have hdecay1 : ∀ η > 0, ∃ δ > 0, ∀ k z,
      z ∈ Γᶜ → z ∈ tsupport (ψ k) → Metric.infDist z Γ < δ →
        ‖iteratedFDeriv ℝ 1 (ψ k) z‖ / Metric.infDist z Γ ^ 1 < η := by
    intro η hη
    obtain ⟨δ, hδ, hbound⟩ := hderivDecay η hη
    refine ⟨δ, hδ, ?_⟩
    intro k z hzΓ hzk hzδ
    simpa only [norm_iteratedFDeriv_one, pow_one] using hbound k z hzΓ hzk hzδ
  have hvalueIterated := tendsto_norm_iteratedFDeriv_finsum_div_infDist_pow
    2 0 2 Γ x ρ ψ hΓ hcluster hρ hρ0 hballs hsupport hsmooth hj0 hdecay0
  have hderivIterated := tendsto_norm_iteratedFDeriv_finsum_div_infDist_pow
    2 1 1 Γ x ρ ψ hΓ hcluster hρ hρ0 hballs hsupport hsmooth hj1 hdecay1
  have hvalue : Tendsto (fun z ↦ ‖∑ᶠ k, ψ k z‖ / Metric.infDist z Γ ^ 2)
      (Filter.comap (fun z ↦ Metric.infDist z Γ) (𝓝 0) ⊓ Filter.principal Γᶜ)
      (𝓝 0) := by
    simpa only [norm_iteratedFDeriv_zero] using hvalueIterated
  have hderiv : Tendsto (fun z ↦ ‖fderiv ℝ (fun w ↦ ∑ᶠ k, ψ k w) z‖ /
      Metric.infDist z Γ)
      (Filter.comap (fun z ↦ Metric.infDist z Γ) (𝓝 0) ⊓ Filter.principal Γᶜ)
      (𝓝 0) := by
    simpa only [norm_iteratedFDeriv_one, pow_one] using hderivIterated
  have htwo : (2 : WithTop ℕ∞) ≠ 0 := by norm_num
  have hsmoothOutside : ContDiffOn ℝ 2 (fun z ↦ ∑ᶠ k, ψ k z) Γᶜ :=
    contDiffOn_finsum_outside 2 Γ x ρ ψ hΓ hcluster hρ0 hsupport hsmooth
  have hdiffOutside : DifferentiableOn ℝ (fun z ↦ ∑ᶠ k, ψ k z) Γᶜ :=
    hsmoothOutside.differentiableOn htwo
  have hvalueEqOn : EqOn (Γᶜ.indicator (fun z ↦ ∑ᶠ k, ψ k z)) 0 Γ :=
    Set.indicator_compl_eqOn_zero Γ (fun z ↦ ∑ᶠ k, ψ k z)
  have hfirstEqOn : EqOn
      (fderiv ℝ (Γᶜ.indicator (fun z ↦ ∑ᶠ k, ψ k z))) 0 Γ :=
    IsClosed.fderiv_indicator_compl_eqOn_zero_of_quadratic_value_decay Γ
      (fun z ↦ ∑ᶠ k, ψ k z) hΓ hdiffOutside hvalue
  have hsecondEqOn : EqOn
      (fderiv ℝ (fderiv ℝ (Γᶜ.indicator (fun z ↦ ∑ᶠ k, ψ k z)))) 0 Γ :=
    IsClosed.fderiv_fderiv_indicator_compl_eqOn_zero Γ
      (fun z ↦ ∑ᶠ k, ψ k z) hΓ hsmoothOutside hvalue hderiv
  constructor
  · exact hcont
  constructor
  · exact hvalueEqOn
  constructor
  · exact hfirstEqOn
  · exact hsecondEqOn

/-- In the Euclidean plane, the same supportwise decay certificate also gives vanishing
gradient and operator-valued Hessian on the closed cluster set. -/
theorem EuclideanPlane.contDiff_two_indicator_compl_finsum_eqOn_zero_jets
    (Γ : Set (EuclideanSpace ℝ (Fin 2))) (x : ℕ → EuclideanSpace ℝ (Fin 2))
    (ρ : ℕ → ℝ) (ψ : ℕ → EuclideanSpace ℝ (Fin 2) → ℝ) (hΓ : IsClosed Γ)
    (hcluster : ∀ y, MapClusterPt y atTop x → y ∈ Γ) (hρ : ∀ k, 0 ≤ ρ k)
    (hρ0 : Tendsto ρ atTop (𝓝 0))
    (hballs : Set.univ.PairwiseDisjoint (fun k ↦ Metric.closedBall (x k) (ρ k)))
    (hsupport : ∀ k, tsupport (ψ k) ⊆ Metric.closedBall (x k) (ρ k))
    (hsmooth : ∀ k, ContDiff ℝ 2 (ψ k))
    (hvalueDecay : ∀ η > 0, ∃ δ > 0, ∀ k z,
      z ∈ Γᶜ → z ∈ tsupport (ψ k) → Metric.infDist z Γ < δ →
        ‖ψ k z‖ / Metric.infDist z Γ ^ 2 < η)
    (hderivDecay : ∀ η > 0, ∃ δ > 0, ∀ k z,
      z ∈ Γᶜ → z ∈ tsupport (ψ k) → Metric.infDist z Γ < δ →
        ‖fderiv ℝ (ψ k) z‖ / Metric.infDist z Γ < η)
    (hsecondDecay : ∀ η > 0, ∃ δ > 0, ∀ k z,
      z ∈ Γᶜ → z ∈ tsupport (ψ k) → Metric.infDist z Γ < δ →
        ‖fderiv ℝ (fderiv ℝ (ψ k)) z‖ < η) :
    ContDiff ℝ 2 (Γᶜ.indicator fun z ↦ ∑ᶠ k, ψ k z) ∧
      EqOn (Γᶜ.indicator (fun z ↦ ∑ᶠ k, ψ k z)) 0 Γ ∧
      EqOn (gradient (Γᶜ.indicator (fun z ↦ ∑ᶠ k, ψ k z))) 0 Γ ∧
      EqOn (EuclideanPlane.hessian (Γᶜ.indicator (fun z ↦ ∑ᶠ k, ψ k z))) 0 Γ := by
  have hcertificate := _root_.contDiff_two_indicator_compl_finsum_eqOn_zero_jets Γ x ρ ψ hΓ
    hcluster hρ hρ0 hballs hsupport hsmooth hvalueDecay hderivDecay hsecondDecay
  have hgradient : EqOn (gradient (Γᶜ.indicator (fun z ↦ ∑ᶠ k, ψ k z))) 0 Γ := by
    intro z hz
    have hfirst := hcertificate.2.2.1 hz
    rw [gradient, hfirst]
    simp
  have hhessian : EqOn
      (EuclideanPlane.hessian (Γᶜ.indicator (fun z ↦ ∑ᶠ k, ψ k z))) 0 Γ := by
    intro z hz
    have hsecond := hcertificate.2.2.2 hz
    apply ContinuousLinearMap.ext
    intro u
    apply ext_inner_left ℝ
    intro v
    rw [real_inner_comm ((EuclideanPlane.hessian
      (Γᶜ.indicator (fun z ↦ ∑ᶠ k, ψ k z)) z) u) v,
      EuclideanPlane.hessian_apply_inner, iteratedFDeriv_two_apply, hsecond]
    simp
  constructor
  · exact hcertificate.1
  constructor
  · exact hcertificate.2.1
  constructor
  · exact hgradient
  · exact hhessian

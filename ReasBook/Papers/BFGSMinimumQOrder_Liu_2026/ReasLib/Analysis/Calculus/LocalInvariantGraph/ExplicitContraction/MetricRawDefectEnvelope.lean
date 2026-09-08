module

public import ReasLib.Analysis.Calculus.LocalCutoff.GraphJetTransform.RadiusEnvelope
public import ReasLib.Analysis.Calculus.LocalCutoff.GraphJetTransform.ProofSupport.RawDefectDerivativeBridge

public section

noncomputable section

open Filter Set
open scoped Topology

universe u

namespace LocalCutoff.GraphTransform

variable {Y : Type u} [NormedAddCommGroup Y]

/-- Helper for Infrastructure I.16a: the range of norms of a two-variable raw defect over all
base points and all increments of norm at most the prescribed radius. -/
private def rawDefectRadiusRange (raw : ℝ → ℝ → Y) (x : ℝ) : Set ℝ :=
  {z | ∃ u h : ℝ, ‖h‖ ≤ x ∧ z = ‖raw u h‖}

/-- Helper for Infrastructure I.16a: the local supremum envelope of a raw defect, capped by its
uniform bound outside the radius on which that bound is certified. -/
private def localRawDefectEnvelope
    (raw : ℝ → ℝ → Y) (cutoff bound x : ℝ) : ℝ :=
  if x < cutoff then sSup (rawDefectRadiusRange raw x) else bound

/-- Helper for Infrastructure I.16a: a raw defect vanishing at zero gives a nonempty radius
range at every nonnegative radius. -/
private theorem rawDefectRadiusRange_nonempty
    {raw : ℝ → ℝ → Y}
    (hzero : ∀ u, raw u 0 = 0) {x : ℝ} (hx : 0 ≤ x) :
    (rawDefectRadiusRange raw x).Nonempty := by
  refine ⟨0, ?_⟩
  refine ⟨0, 0, ?_, ?_⟩
  · simpa only [norm_zero] using hx
  · rw [hzero, norm_zero]

/-- Helper for Infrastructure I.16a: a uniform raw-defect bound on a radius bounds the
corresponding set of defect norms from above. -/
private theorem rawDefectRadiusRange_bddAbove
    {raw : ℝ → ℝ → Y} {cutoff bound x : ℝ}
    (hx : x < cutoff)
    (hbound : ∀ u h : ℝ, ‖h‖ < cutoff → ‖raw u h‖ ≤ bound) :
    BddAbove (rawDefectRadiusRange raw x) := by
  refine ⟨bound, ?_⟩
  intro z hz
  obtain ⟨u, h, hh, rfl⟩ := hz
  exact hbound u h (hh.trans_lt hx)

/-- Helper for Infrastructure I.16a: below its cutoff, the capped local envelope is the
supremum of the raw-defect radius range. -/
private theorem localRawDefectEnvelope_eq_sSup
    (raw : ℝ → ℝ → Y) {cutoff bound x : ℝ} (hx : x < cutoff) :
    localRawDefectEnvelope raw cutoff bound x = sSup (rawDefectRadiusRange raw x) := by
  rw [localRawDefectEnvelope, if_pos hx]

/-- Helper for Infrastructure I.16a: the capped local raw-defect envelope is nonnegative at
every nonnegative radius. -/
private theorem localRawDefectEnvelope_nonneg
    {raw : ℝ → ℝ → Y} {cutoff bound x : ℝ}
    (hzero : ∀ u, raw u 0 = 0) (hbound_nonneg : 0 ≤ bound)
    (hbound : ∀ u h : ℝ, ‖h‖ < cutoff → ‖raw u h‖ ≤ bound)
    (hx : 0 ≤ x) :
    0 ≤ localRawDefectEnvelope raw cutoff bound x := by
  by_cases hx_cutoff : x < cutoff
  · rw [localRawDefectEnvelope_eq_sSup raw hx_cutoff]
    have hrange_bdd : BddAbove (rawDefectRadiusRange raw x) :=
      rawDefectRadiusRange_bddAbove hx_cutoff hbound
    apply le_csSup hrange_bdd
    refine ⟨0, 0, ?_, ?_⟩
    · simpa only [norm_zero] using hx
    · rw [hzero, norm_zero]
  · rw [localRawDefectEnvelope, if_neg hx_cutoff]
    exact hbound_nonneg

/-- Helper for Infrastructure I.16a: on its certified radius, the capped local raw-defect
envelope is bounded by the selected uniform bound. -/
private theorem localRawDefectEnvelope_le_bound
    {raw : ℝ → ℝ → Y} {cutoff bound x : ℝ}
    (hzero : ∀ u, raw u 0 = 0) (hx_nonneg : 0 ≤ x) (hx : x < cutoff)
    (hbound : ∀ u h : ℝ, ‖h‖ < cutoff → ‖raw u h‖ ≤ bound) :
    localRawDefectEnvelope raw cutoff bound x ≤ bound := by
  rw [localRawDefectEnvelope_eq_sSup raw hx]
  apply csSup_le (rawDefectRadiusRange_nonempty hzero hx_nonneg)
  intro z hz
  obtain ⟨u, h, hh, rfl⟩ := hz
  exact hbound u h (hh.trans_lt hx)

/-- Helper for Infrastructure I.16a: the capped local raw-defect envelope is monotone on
nonnegative radii. -/
private theorem localRawDefectEnvelope_mono
    {raw : ℝ → ℝ → Y} {cutoff bound : ℝ}
    (hzero : ∀ u, raw u 0 = 0)
    (hbound : ∀ u h : ℝ, ‖h‖ < cutoff → ‖raw u h‖ ≤ bound)
    {x y : ℝ} (hx_nonneg : 0 ≤ x) (hxy : x ≤ y) :
    localRawDefectEnvelope raw cutoff bound x ≤
      localRawDefectEnvelope raw cutoff bound y := by
  by_cases hy : y < cutoff
  · have hx : x < cutoff := hxy.trans_lt hy
    rw [localRawDefectEnvelope_eq_sSup raw hx,
      localRawDefectEnvelope_eq_sSup raw hy]
    apply csSup_le (rawDefectRadiusRange_nonempty hzero hx_nonneg)
    intro z hz
    apply le_csSup (rawDefectRadiusRange_bddAbove hy hbound)
    obtain ⟨u, h, hh, rfl⟩ := hz
    exact ⟨u, h, hh.trans hxy, rfl⟩
  · have hy_envelope :
        localRawDefectEnvelope raw cutoff bound y = bound := by
      rw [localRawDefectEnvelope, if_neg hy]
    rw [hy_envelope]
    by_cases hx : x < cutoff
    · exact localRawDefectEnvelope_le_bound hzero hx_nonneg hx hbound
    · rw [localRawDefectEnvelope, if_neg hx]

/-- Helper for Infrastructure I.16a: every sufficiently local raw-defect norm is bounded by
the capped envelope at the norm of its increment. -/
private theorem norm_rawDefect_le_localEnvelope
    {raw : ℝ → ℝ → Y} {cutoff bound : ℝ}
    (hbound : ∀ u h : ℝ, ‖h‖ < cutoff → ‖raw u h‖ ≤ bound)
    (u h : ℝ) (hh : ‖h‖ < cutoff) :
    ‖raw u h‖ ≤ localRawDefectEnvelope raw cutoff bound ‖h‖ := by
  rw [localRawDefectEnvelope_eq_sSup raw hh]
  apply le_csSup (rawDefectRadiusRange_bddAbove hh hbound)
  exact ⟨u, h, le_rfl, rfl⟩

/-- Helper for Infrastructure I.16a: an inverse-coordinate raw recurrence lifts to the capped
supremum envelope recurrence on a sufficiently small radius. -/
private theorem localRawDefectEnvelope_recurrence
    {raw : ℝ → ℝ → Y} {inverse : ℝ → ℝ}
    {cutoff bound p c e : ℝ}
    (hzero : ∀ u, raw u 0 = 0) (hbound_nonneg : 0 ≤ bound)
    (hbound : ∀ u h : ℝ, ‖h‖ < cutoff → ‖raw u h‖ ≤ bound)
    (hp : 0 ≤ p) (hc : 0 < c) (he : 0 < e)
    (hinverse : ∀ u h : ℝ,
      ‖inverse (u + h) - inverse u‖ ≤ c * ‖h‖)
    (hrec : ∃ delta > 0, ∀ u h : ℝ, h ≠ 0 → ‖h‖ < delta →
      ‖raw u h‖ ≤
        p * ‖raw (inverse u) (inverse (u + h) - inverse u)‖ + e * ‖h‖)
    (hcutoff : 0 < cutoff) :
    ∃ delta > 0, ∀ x : ℝ, 0 < x → x < delta →
      localRawDefectEnvelope raw cutoff bound x ≤
        p * localRawDefectEnvelope raw cutoff bound (c * x) + e * x := by
  obtain ⟨recRadius, hrecRadius, hrec_bound⟩ := hrec
  let delta := min recRadius (min cutoff (cutoff / c))
  have hdelta : 0 < delta := by
    exact lt_min hrecRadius (lt_min hcutoff (div_pos hcutoff hc))
  refine ⟨delta, hdelta, ?_⟩
  intro x hx hxdelta
  have hx_rec : x < recRadius := hxdelta.trans_le (min_le_left _ _)
  have hx_cutoff : x < cutoff :=
    hxdelta.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hx_transport : c * x < cutoff := by
    have hx_div : x < cutoff / c :=
      hxdelta.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    have hx_mul : x * c < cutoff := (lt_div_iff₀ hc).mp hx_div
    calc
      c * x = x * c := mul_comm c x
      _ < cutoff := hx_mul
  have hcx_nonneg : 0 ≤ c * x := mul_nonneg hc.le hx.le
  rw [localRawDefectEnvelope_eq_sSup raw hx_cutoff]
  apply csSup_le (rawDefectRadiusRange_nonempty hzero hx.le)
  intro z hz
  obtain ⟨u, h, hh, rfl⟩ := hz
  by_cases hh_zero : h = 0
  · subst h
    rw [hzero, norm_zero]
    exact add_nonneg
      (mul_nonneg hp
        (localRawDefectEnvelope_nonneg hzero hbound_nonneg hbound hcx_nonneg))
      (mul_nonneg he.le hx.le)
  · have hh_rec : ‖h‖ < recRadius := hh.trans_lt hx_rec
    have hraw := hrec_bound u h hh_zero hh_rec
    have htransport : ‖inverse (u + h) - inverse u‖ ≤ c * x := by
      calc
        ‖inverse (u + h) - inverse u‖ ≤ c * ‖h‖ := hinverse u h
        _ ≤ c * x := mul_le_mul_of_nonneg_left hh hc.le
    have htransport_bound :
        ‖raw (inverse u) (inverse (u + h) - inverse u)‖ ≤
          localRawDefectEnvelope raw cutoff bound (c * x) := by
      rw [localRawDefectEnvelope_eq_sSup raw hx_transport]
      apply le_csSup (rawDefectRadiusRange_bddAbove hx_transport hbound)
      exact ⟨inverse u, inverse (u + h) - inverse u, htransport, rfl⟩
    calc
      ‖raw u h‖ ≤
          p * ‖raw (inverse u) (inverse (u + h) - inverse u)‖ + e * ‖h‖ := hraw
      _ ≤ p * localRawDefectEnvelope raw cutoff bound (c * x) + e * x := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left htransport_bound hp)
          (mul_le_mul_of_nonneg_left hh he.le)

/-- Infrastructure I.16a: a locally uniformly bounded raw defect satisfying a uniformly
small inverse-coordinate affine recurrence is little-o of its scalar increment at every base
point, provided both the recurrence factor and its transported factor are strict contractions. -/
theorem rawDefect_isLittleO_of_inverseRecurrence
    (raw : ℝ → ℝ → Y) (inverse : ℝ → ℝ) (p c : ℝ)
    (hzero : ∀ u, raw u 0 = 0)
    (hbounded : ∃ cutoff > 0, ∃ bound ≥ 0,
      ∀ u h : ℝ, ‖h‖ < cutoff → ‖raw u h‖ ≤ bound)
    (hinverse : ∀ u h : ℝ,
      ‖inverse (u + h) - inverse u‖ ≤ c * ‖h‖)
    (hp : 0 ≤ p) (hp_lt : p < 1) (hc : 0 < c) (hpc : p * c < 1)
    (hrec : ∀ e > 0, ∃ delta > 0, ∀ u h : ℝ, h ≠ 0 → ‖h‖ < delta →
      ‖raw u h‖ ≤
        p * ‖raw (inverse u) (inverse (u + h) - inverse u)‖ + e * ‖h‖) :
    ∀ u, (fun h : ℝ ↦ raw u h) =o[𝓝 0] (fun h : ℝ ↦ h) := by
  obtain ⟨cutoff, hcutoff, bound, hbound_nonneg, hbound⟩ := hbounded
  let envelope : ℝ → ℝ := localRawDefectEnvelope raw cutoff bound
  have henvelope_mono : ∀ {x y : ℝ}, 0 ≤ x → x ≤ y → envelope x ≤ envelope y := by
    intro x y hx hxy
    exact localRawDefectEnvelope_mono hzero hbound hx hxy
  have henvelope_bounded :
      ∃ delta > 0, ∃ M ≥ 0, ∀ x, 0 ≤ x → x < delta → envelope x ≤ M := by
    refine ⟨cutoff, hcutoff, bound, hbound_nonneg, ?_⟩
    intro x hx hx_cutoff
    exact localRawDefectEnvelope_le_bound hzero hx hx_cutoff hbound
  have henvelope_recurrence : ∀ e > 0, ∃ delta > 0, ∀ x, 0 < x → x < delta →
      envelope x ≤ p * envelope (c * x) + e * x := by
    intro e he
    exact localRawDefectEnvelope_recurrence hzero hbound_nonneg hbound hp hc he
      hinverse (hrec e he) hcutoff
  have henvelope_sublinear :
      ∀ epsilon > 0, ∃ delta > 0, ∀ x, 0 < x → x < delta →
        envelope x ≤ epsilon * x := by
    exact radiusEnvelope_sublinear_of_recurrence envelope p c henvelope_mono hp hp_lt hc hpc
      henvelope_bounded henvelope_recurrence
  intro u
  rw [Asymptotics.isLittleO_iff]
  intro epsilon hepsilon
  obtain ⟨delta, hdelta, hsublinear⟩ := henvelope_sublinear epsilon hepsilon
  let finalRadius := min delta cutoff
  have hfinalRadius : 0 < finalRadius := lt_min hdelta hcutoff
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hfinalRadius] with h hh
  have hh_final : ‖h‖ < finalRadius := by
    simpa only [Metric.mem_ball, dist_zero_right] using hh
  by_cases hh_zero : h = 0
  · subst h
    rw [hzero, norm_zero]
    exact mul_nonneg hepsilon.le (norm_nonneg (0 : ℝ))
  · have hh_pos : 0 < ‖h‖ := norm_pos_iff.mpr hh_zero
    have hh_delta : ‖h‖ < delta := hh_final.trans_le (min_le_left _ _)
    have hh_cutoff : ‖h‖ < cutoff := hh_final.trans_le (min_le_right _ _)
    calc
      ‖raw u h‖ ≤ envelope ‖h‖ :=
        norm_rawDefect_le_localEnvelope hbound u h hh_cutoff
      _ ≤ epsilon * ‖h‖ := hsublinear ‖h‖ hh_pos hh_delta

end LocalCutoff.GraphTransform

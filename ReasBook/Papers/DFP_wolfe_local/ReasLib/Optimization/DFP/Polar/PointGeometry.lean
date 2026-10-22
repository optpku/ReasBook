/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/DFP_wolfe_local/README.md (Contributors).
-/

module

public import ReasLib.Optimization.DFP.Polar.RadiusProducts
public import ReasLib.Optimization.DFP.Polar.AngularGeometry
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.Polar.PointGeometry

open AngularGeometry RadiusProducts

/-- Helper for lem:polar-geometry: the original polar direction has Euclidean norm one. -/
theorem polarUnit_norm (θ : ℝ) : ‖polarUnit θ‖ = 1 := by
  have hsquare : ‖polarUnit θ‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [Fin.sum_univ_two, polarUnit_apply_zero, polarUnit_apply_one]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  nlinarith [norm_nonneg (polarUnit θ)]

/-- Helper for lem:polar-geometry: the Euclidean norm of an actual point is its
original nonnegative tail-product radius. -/
theorem point_norm (p : Parameters) (k : ℕ) (hr : 0 ≤ p.radius k) :
    ‖p.point k‖ = p.radius k := by
  rw [Parameters.point_def, norm_smul, polarUnit_norm, Real.norm_eq_abs,
    abs_of_nonneg hr, mul_one]

/-- Helper for eq:polar-chord: the exact source chord identity for the actual points,
with the original unreduced real angles. -/
theorem point_chord_sq (p : Parameters) (k m : ℕ) :
    ‖p.point m - p.point k‖ ^ 2 = (p.radius m - p.radius k) ^ 2 +
      4 * p.radius m * p.radius k * Real.sin ((p.angle m - p.angle k) / 2) ^ 2 := by
  rw [Parameters.point_def, Parameters.point_def]
  exact polar_chord_sq _ _ _ _

/-- Helper for lem:polar-geometry: the difference of two actual nonnegative radii
is bounded by the Euclidean distance between the actual points. -/
theorem radius_sub_le_point_distance (p : Parameters) (k m : ℕ)
    (hk : 0 ≤ p.radius k) (hm : 0 ≤ p.radius m) :
    p.radius k - p.radius m ≤ ‖p.point m - p.point k‖ := by
  have h := norm_sub_norm_le (p.point k) (p.point m)
  rw [point_norm p k hk, point_norm p m hm, norm_sub_rev] at h
  exact h

/-- Helper for lem:polar-geometry: the Euclidean unit-vector chord is bounded by
the difference of its original real angles. -/
theorem polarUnit_sub_norm_le (θ φ : ℝ) :
    ‖polarUnit θ - polarUnit φ‖ ≤ |θ - φ| := by
  have hchord : ‖polarUnit θ - polarUnit φ‖ ^ 2 =
      4 * Real.sin ((θ - φ) / 2) ^ 2 := by
    simpa only [one_smul, sub_self, zero_pow two_ne_zero, one_mul, mul_one, zero_add]
      using polar_chord_sq 1 1 θ φ
  have hsinBound : |Real.sin ((θ - φ) / 2)| ≤ |(θ - φ) / 2| := Real.abs_sin_le_abs
  have hsin := pow_le_pow_left₀ (abs_nonneg _) hsinBound 2
  simp only [sq_abs] at hsin
  apply (sq_le_sq₀ (norm_nonneg _) (abs_nonneg _)).mp
  rw [sq_abs, hchord]
  nlinarith

/-- Helper for eq:polar-chord and eq:polar-separation: for radii at least one and
angular span in `[0,π]`, the exact source chord controls that span linearly. -/
theorem polarChord_angle_lower (r s θ φ : ℝ) (hr : 1 ≤ r) (hs : 1 ≤ s)
    (hangle : 0 ≤ θ - φ) (hspan : θ - φ ≤ Real.pi) :
    (2 / Real.pi) * (θ - φ) ≤ ‖r • polarUnit θ - s • polarUnit φ‖ := by
  have hhalf : 0 ≤ (θ - φ) / 2 := by linarith
  have hhalfPi : (θ - φ) / 2 ≤ Real.pi / 2 := by linarith
  have hsinLower := Real.mul_le_sin hhalf hhalfPi
  have hsinNonneg : 0 ≤ Real.sin ((θ - φ) / 2) := by
    have hPi : (θ - φ) / 2 ≤ Real.pi := by linarith [Real.pi_pos]
    exact Real.sin_nonneg_of_nonneg_of_le_pi hhalf hPi
  have hrs : 1 ≤ r * s := one_le_mul_of_one_le_of_one_le hr hs
  have hfour : (0 : ℝ) ≤ 4 := by norm_num
  have hterm := mul_le_mul_of_nonneg_right hrs
    (mul_nonneg hfour (sq_nonneg (Real.sin ((θ - φ) / 2))))
  have hnormSquare : (2 * Real.sin ((θ - φ) / 2)) ^ 2 ≤
      ‖r • polarUnit θ - s • polarUnit φ‖ ^ 2 := by
    rw [polar_chord_sq]
    nlinarith [sq_nonneg (r - s)]
  have hnorm := (sq_le_sq₀ (mul_nonneg zero_le_two hsinNonneg) (norm_nonneg _)).mp hnormSquare
  calc
    (2 / Real.pi) * (θ - φ) = 2 * ((2 / Real.pi) * ((θ - φ) / 2)) := by ring
    _ ≤ 2 * Real.sin ((θ - φ) / 2) := mul_le_mul_of_nonneg_left hsinLower zero_le_two
    _ ≤ ‖r • polarUnit θ - s • polarUnit φ‖ := hnorm

/-- Helper for lem:polar-geometry: radial displacement and real angular displacement
control the distance of two original polar points. -/
theorem polarChord_upper (r s θ φ : ℝ) (hs : 0 ≤ s) :
    ‖r • polarUnit θ - s • polarUnit φ‖ ≤ |r - s| + s * |θ - φ| := by
  have hdecomposition : r • polarUnit θ - s • polarUnit φ =
      (r - s) • polarUnit θ + s • (polarUnit θ - polarUnit φ) := by module
  rw [hdecomposition]
  calc
    ‖(r - s) • polarUnit θ + s • (polarUnit θ - polarUnit φ)‖ ≤
        ‖(r - s) • polarUnit θ‖ + ‖s • (polarUnit θ - polarUnit φ)‖ := norm_add_le _ _
    _ = |r - s| + s * ‖polarUnit θ - polarUnit φ‖ := by
      rw [norm_smul, norm_smul, polarUnit_norm, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hs, mul_one]
    _ ≤ |r - s| + s * |θ - φ| :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (polarUnit_sub_norm_le θ φ) hs)

/-- Helper for eq:polar-separation: the positive fixed angular separation constant
for the original near-window argument. -/
def nearSeparationConstant : ℝ := (2 / Real.pi) * (3 * baseAngle / 28)

/-- Helper for eq:polar-separation: the explicit fixed near-window coefficient. -/
theorem nearSeparationConstant_def :
    nearSeparationConstant = (2 / Real.pi) * (3 * baseAngle / 28) := by rfl

/-- Helper for eq:polar-separation: the angular near-window coefficient is positive. -/
theorem nearSeparationConstant_pos : 0 < nearSeparationConstant := by
  rw [nearSeparationConstant_def]
  have ha := baseAngle_pos
  positivity

/-- Helper for eq:polar-separation: within the source near window, the actual
point distance controls `(m-k)t²` by the sine lower bound and exact chord identity. -/
theorem near_point_separation (p : Parameters) (hstart : 0 < p.startIndex)
    (habove : ∀ k, 1 ≤ p.radius k) (k m : ℕ) (hkm : k < m)
    (hwindow : m - k ≤ nearWindow p k) :
    nearSeparationConstant * (m - k : ℕ) * p.scale (k / 2) ^ 2 ≤
      ‖p.point m - p.point k‖ := by
  have hangle := nearWindow_angle_bounds p hstart k m hkm hwindow
  have hnonneg := sub_nonneg.mpr ((angle_strictMono p hstart) hkm).le
  have hspan := hangle.2.1.trans hangle.2.2
  have hchord := polarChord_angle_lower (p.radius m) (p.radius k) (p.angle m) (p.angle k)
    (habove m) (habove k) hnonneg hspan
  rw [← Parameters.point_def, ← Parameters.point_def] at hchord
  have hcoefficient : 0 ≤ 2 / Real.pi := (div_pos zero_lt_two Real.pi_pos).le
  have hlower := mul_le_mul_of_nonneg_left hangle.1 hcoefficient
  rw [nearSeparationConstant_def]
  calc
    (2 / Real.pi * (3 * baseAngle / 28)) * (m - k : ℕ) * p.scale (k / 2) ^ 2 =
        (2 / Real.pi) * ((3 * baseAngle / 28) * (m - k : ℕ) * p.scale (k / 2) ^ 2) := by ring
    _ ≤ (2 / Real.pi) * (p.angle m - p.angle k) := hlower
    _ ≤ ‖p.point m - p.point k‖ := hchord

/-- Helper for eq:polar-separation: after the fixed scale cutoff `t≤1/4`, the
original floor window has at least half its defining size, in squared-scale form. -/
theorem nearWindow_mul_scale_sq_lower (p : Parameters) (hstart : 0 < p.startIndex)
    (hsmall : p.scale 0 ≤ 1 / 4) (k : ℕ) :
    (1 / 8 : ℝ) ≤ (nearWindow p k : ℝ) * p.scale (k / 2) ^ 2 := by
  have ht := ScaleTails.scale_pos p hstart (k / 2)
  have htsmall := (ScaleTails.scale_antitone p hstart (Nat.zero_le (k / 2))).trans hsmall
  have hsquare : p.scale (k / 2) ^ 2 ≤ 1 / 8 := by nlinarith
  have hfloor := Nat.lt_floor_add_one ((1 / 4 : ℝ) * p.scale (k / 2) ^ (-2 : ℤ))
  have hmul := mul_lt_mul_of_pos_right hfloor (sq_pos_of_pos ht)
  have hcancel : ((1 / 4 : ℝ) * p.scale (k / 2) ^ (-2 : ℤ)) *
      p.scale (k / 2) ^ 2 = 1 / 4 := by field_simp [ht.ne']
  rw [hcancel, ← nearWindow_def] at hmul
  nlinarith

/-- Helper for eq:polar-separation: the original source floor window satisfies
`M≥ηt⁻²/2` with the same fixed `η=1/4`. -/
theorem nearWindow_lower (p : Parameters) (hstart : 0 < p.startIndex)
    (hsmall : p.scale 0 ≤ 1 / 4) (k : ℕ) :
    (1 / 8 : ℝ) * p.scale (k / 2) ^ (-2 : ℤ) ≤ (nearWindow p k : ℝ) := by
  have ht := ScaleTails.scale_pos p hstart (k / 2)
  have h := nearWindow_mul_scale_sq_lower p hstart hsmall k
  have hinverse : (1 / 8 : ℝ) * p.scale (k / 2) ^ (-2 : ℤ) =
      (1 / 8 : ℝ) / p.scale (k / 2) ^ 2 := by field_simp [ht.ne']
  rw [hinverse]
  exact (div_le_iff₀ (sq_pos_of_pos ht)).mpr h

/-- Helper for eq:polar-separation: throughout the original near window the
quartic scales are at least one sixteenth of the initial quartic scale. -/
theorem scale_fourth_nearWindow_lower (p : Parameters) (hstart : 0 < p.startIndex)
    (k l : ℕ) (hkl : k ≤ l) (hl : l ≤ k + nearWindow p k) :
    (1 / 16 : ℝ) * p.scale (k / 2) ^ 4 ≤ p.scale (l / 2) ^ 4 := by
  have hwindow : k + nearWindow p k - k ≤ nearWindow p k := by omega
  have hscale := (scale_sq_nearWindow_bounds p hstart k (k + nearWindow p k) l
    (Nat.le_add_right _ _) hwindow hkl hl).1
  have hnonneg : 0 ≤ (1 / 4 : ℝ) * p.scale (k / 2) ^ 2 := by positivity
  have hsquare := pow_le_pow_left₀ hnonneg hscale 2
  nlinarith

/-- Helper for eq:polar-separation: the actual radial decrements telescope over
every finite index interval. -/
theorem sum_radius_drop_Ico (p : Parameters) (k m : ℕ) (hkm : k ≤ m) :
    (∑ h ∈ Finset.Ico k m, (p.radius h - p.radius (h + 1))) = p.radius k - p.radius m := by
  have h := Finset.sum_Ico_sub p.radius hkm
  rw [Finset.sum_sub_distrib] at h ⊢
  linarith

/-- Helper for eq:polar-separation: the first full near window of quartic radial
decrements already separates every later point, independently of its final angle. -/
theorem far_point_separation (p : Parameters) (hstart : 0 < p.startIndex)
    (hsmall : p.scale 0 ≤ 1 / 4) (habove : ∀ k, 1 ≤ p.radius k)
    (hanti : Antitone p.radius) (c : ℝ) (hc : 0 ≤ c)
    (hdrop : ∀ k, c * p.scale (k / 2) ^ 4 ≤ p.radius k - p.radius (k + 1))
    (k m : ℕ) (hwindow : k + nearWindow p k ≤ m) :
    (c / 128) * p.scale (k / 2) ^ 2 ≤ ‖p.point m - p.point k‖ := by
  have hlocal (l : ℕ) (hl : l ∈ Finset.Ico k (k + nearWindow p k)) :
      (c / 16) * p.scale (k / 2) ^ 4 ≤ p.radius l - p.radius (l + 1) := by
    have hb := Finset.mem_Ico.mp hl
    have hscale := scale_fourth_nearWindow_lower p hstart k l hb.1 hb.2.le
    have hmul := mul_le_mul_of_nonneg_left hscale hc
    calc
      (c / 16) * p.scale (k / 2) ^ 4 = c * ((1 / 16) * p.scale (k / 2) ^ 4) := by ring
      _ ≤ c * p.scale (l / 2) ^ 4 := hmul
      _ ≤ p.radius l - p.radius (l + 1) := hdrop l
  have hsum := Finset.sum_le_sum hlocal
  rw [sum_radius_drop_Ico p k (k + nearWindow p k) (Nat.le_add_right _ _)] at hsum
  simp only [Finset.sum_const, nsmul_eq_mul, Nat.card_Ico, Nat.add_sub_cancel_left] at hsum
  have hfloor := nearWindow_mul_scale_sq_lower p hstart hsmall k
  have hsixteen : (0 : ℝ) ≤ 16 := by norm_num
  have hscaled := mul_le_mul_of_nonneg_right hfloor
    (mul_nonneg (div_nonneg hc hsixteen)
      (sq_nonneg (p.scale (k / 2))))
  have hfirst : (c / 128) * p.scale (k / 2) ^ 2 ≤
      p.radius k - p.radius (k + nearWindow p k) := by
    nlinarith [hscaled]
  have hradial : p.radius k - p.radius (k + nearWindow p k) ≤ p.radius k - p.radius m := by
    linarith [hanti hwindow]
  exact hfirst.trans (hradial.trans
    (radius_sub_le_point_distance p k m (zero_le_one.trans (habove k))
      (zero_le_one.trans (habove m))))

/-- Helper for lem:polar-geometry: every unit Euclidean planar vector is an
original polar direction, using the usual complex argument coordinates. -/
theorem exists_polarUnit_of_norm_eq_one (x : EuclideanSpace ℝ (Fin 2)) (hx : ‖x‖ = 1) :
    ∃ φ : ℝ, polarUnit φ = x := by
  let z : ℂ := ⟨x 0, x 1⟩
  have hcoordinates : x 0 ^ 2 + x 1 ^ 2 = 1 := by
    have hsquare := congrArg (fun u : ℝ ↦ u ^ 2) hx
    rw [EuclideanSpace.real_norm_sq_eq] at hsquare
    simpa only [Fin.sum_univ_two, one_pow] using hsquare
  have hnorm : ‖z‖ = 1 := by
    have hsquare := Complex.sq_norm z
    simp only [Complex.normSq_apply, z] at hsquare
    nlinarith [norm_nonneg z]
  have hne : z ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [hnorm]
    exact one_ne_zero
  refine ⟨z.arg, ?_⟩
  apply PiLp.ext
  rw [Fin.forall_fin_two]
  constructor
  · rw [polarUnit_apply_zero, Complex.cos_arg hne, hnorm, div_one]
  · rw [polarUnit_apply_one, Complex.sin_arg, hnorm, div_one]

/-- Helper for lem:polar-geometry: the actual points along the source's first
crossings converge to each specified unit direction as the original radii tend to one. -/
theorem exists_point_firstCrossings (p : Parameters) (hstart : 0 < p.startIndex)
    (hradius : Tendsto p.radius atTop (𝓝 1)) (φ : ℝ) :
    ∃ N : ℕ, ∃ j : ℕ → ℕ,
      StrictMono j ∧
      (∀ n, φ + ((N + n : ℕ) : ℝ) * (2 * Real.pi) ≤ p.angle (j n)) ∧
      (∀ n k, k < j n → p.angle k < φ + ((N + n : ℕ) : ℝ) * (2 * Real.pi)) ∧
      Tendsto (fun n ↦ p.angle (j n) - (φ + ((N + n : ℕ) : ℝ) * (2 * Real.pi)))
        atTop (𝓝 0) ∧
      Tendsto (p.point ∘ j) atTop (𝓝 (polarUnit φ)) := by
  obtain ⟨N, j, hstrict, hj, _, hcross, hbefore, hover, hunit⟩ :=
    exists_directional_firstCrossings p hstart φ
  have hpoint := (hradius.comp hj).smul hunit
  have hlimit : Tendsto (p.point ∘ j) atTop (𝓝 (polarUnit φ)) := by
    simpa only [Function.comp_def, Parameters.point_def, one_smul] using hpoint
  exact ⟨N, j, hstrict, hcross, hbefore, hover, hlimit⟩

/-- Helper for lem:polar-geometry: every cluster point of the original actual
points lies on the unit circle because their norms are their radii. -/
theorem clusterPoint_norm_eq_one (p : Parameters) (hr : ∀ k, 0 ≤ p.radius k)
    (hradius : Tendsto p.radius atTop (𝓝 1)) (x : EuclideanSpace ℝ (Fin 2))
    (hx : MapClusterPt x atTop p.point) : ‖x‖ = 1 := by
  obtain ⟨j, hstrict, hj⟩ := hx.tendsto_subseq
  have hnorm := hj.norm
  have hunit : Tendsto (fun n ↦ ‖p.point (j n)‖) atTop (𝓝 1) := by
    simpa only [Function.comp_def, point_norm p _ (hr _)] using hradius.comp hstrict.tendsto_atTop
  exact tendsto_nhds_unique hnorm hunit

/-- Helper for lem:polar-geometry: the original points have exactly the unit
circle as their cluster set, with every circle point obtained from first crossings. -/
theorem point_cluster_iff (p : Parameters) (hstart : 0 < p.startIndex)
    (hr : ∀ k, 0 ≤ p.radius k) (hradius : Tendsto p.radius atTop (𝓝 1))
    (x : EuclideanSpace ℝ (Fin 2)) : MapClusterPt x atTop p.point ↔ ‖x‖ = 1 := by
  constructor
  · exact clusterPoint_norm_eq_one p hr hradius x
  · intro hx
    obtain ⟨φ, hφ⟩ := exists_polarUnit_of_norm_eq_one x hx
    obtain ⟨N, j, hstrict, _, _, _, hlimit⟩ := exists_point_firstCrossings p hstart hradius φ
    rw [hφ] at hlimit
    exact MapClusterPt.of_comp hstrict.tendsto_atTop hlimit.mapClusterPt

/-- Helper for lem:polar-geometry: as a set, the cluster set of the original
actual sequence is exactly the Euclidean unit circle. -/
theorem point_clusterSet (p : Parameters) (hstart : 0 < p.startIndex)
    (hr : ∀ k, 0 ≤ p.radius k) (hradius : Tendsto p.radius atTop (𝓝 1)) :
    {x | MapClusterPt x atTop p.point} = Metric.sphere 0 1 := by
  ext x
  simp only [Set.mem_setOf_eq, point_cluster_iff p hstart hr hradius, Metric.mem_sphere,
    dist_zero_right]

/-- Helper for eq:polar-separation: the original floor window is nonempty
after the same fixed scale cutoff used for its half-size lower bound. -/
theorem nearWindow_pos (p : Parameters) (hstart : 0 < p.startIndex)
    (hsmall : p.scale 0 ≤ 1 / 4) (k : ℕ) : 0 < nearWindow p k := by
  have ht := ScaleTails.scale_pos p hstart (k / 2)
  have hpositive : 0 < (1 / 8 : ℝ) * p.scale (k / 2) ^ (-2 : ℤ) := by positivity
  exact Nat.cast_pos.mp (hpositive.trans_le (nearWindow_lower p hstart hsmall k))

/-- Helper for eq:polar-separation: the near angular estimate and the first-window
radial sum give one ordered-pair separation bound without any final-angle restriction. -/
theorem ordered_point_separation (p : Parameters) (hstart : 0 < p.startIndex)
    (hsmall : p.scale 0 ≤ 1 / 4) (habove : ∀ k, 1 ≤ p.radius k)
    (hanti : Antitone p.radius) (c : ℝ) (hc : 0 ≤ c)
    (hdrop : ∀ k, c * p.scale (k / 2) ^ 4 ≤ p.radius k - p.radius (k + 1))
    (k m : ℕ) (hkm : k < m) :
    min nearSeparationConstant (c / 128) * p.scale (k / 2) ^ 2 ≤
      ‖p.point m - p.point k‖ := by
  by_cases hnear : m - k ≤ nearWindow p k
  · have hbound := near_point_separation p hstart habove k m hkm hnear
    have hcount : (1 : ℝ) ≤ (m - k : ℕ) := by
      exact_mod_cast Nat.succ_le_of_lt (Nat.sub_pos_of_lt hkm)
    have hcoefficient : 0 ≤ nearSeparationConstant * p.scale (k / 2) ^ 2 :=
      mul_nonneg nearSeparationConstant_pos.le (sq_nonneg _)
    have hcountBound := mul_le_mul_of_nonneg_left hcount hcoefficient
    have hmin := mul_le_mul_of_nonneg_right
      (min_le_left nearSeparationConstant (c / 128)) (sq_nonneg (p.scale (k / 2)))
    calc
      min nearSeparationConstant (c / 128) * p.scale (k / 2) ^ 2 ≤
          nearSeparationConstant * p.scale (k / 2) ^ 2 := hmin
      _ ≤ nearSeparationConstant * (m - k : ℕ) * p.scale (k / 2) ^ 2 := by
        nlinarith [hcountBound]
      _ ≤ ‖p.point m - p.point k‖ := hbound
  · have hwindow : k + nearWindow p k ≤ m := by omega
    have hfar := far_point_separation p hstart hsmall habove hanti c hc hdrop k m hwindow
    have hmin := mul_le_mul_of_nonneg_right
      (min_le_right nearSeparationConstant (c / 128)) (sq_nonneg (p.scale (k / 2)))
    exact hmin.trans hfar

/-- Helper for eq:polar-separation: interchanging the two indices gives the exact
source maximum of squared scales for every pair of distinct actual points. -/
theorem point_separation (p : Parameters) (hstart : 0 < p.startIndex)
    (hsmall : p.scale 0 ≤ 1 / 4) (habove : ∀ k, 1 ≤ p.radius k)
    (hanti : Antitone p.radius) (c : ℝ) (hc : 0 ≤ c)
    (hdrop : ∀ k, c * p.scale (k / 2) ^ 4 ≤ p.radius k - p.radius (k + 1))
    (k m : ℕ) (hne : k ≠ m) :
    min nearSeparationConstant (c / 128) *
        max (p.scale (k / 2) ^ 2) (p.scale (m / 2) ^ 2) ≤ ‖p.point m - p.point k‖ := by
  rcases lt_or_gt_of_ne hne with hkm | hmk
  · have hcycle : k / 2 ≤ m / 2 := Nat.div_le_div_right hkm.le
    have hscale := ScaleTails.scale_antitone p hstart hcycle
    have hsquare := pow_le_pow_left₀ (ScaleTails.scale_nonneg p _) hscale 2
    rw [max_eq_left hsquare]
    exact ordered_point_separation p hstart hsmall habove hanti c hc hdrop k m hkm
  · have hcycle : m / 2 ≤ k / 2 := Nat.div_le_div_right hmk.le
    have hscale := ScaleTails.scale_antitone p hstart hcycle
    have hsquare := pow_le_pow_left₀ (ScaleTails.scale_nonneg p _) hscale 2
    rw [max_eq_right hsquare, norm_sub_rev]
    exact ordered_point_separation p hstart hsmall habove hanti c hc hdrop m k hmk

/-- Helper for eq:polar-orders: every actual one-step Euclidean displacement has
the source quadratic lower bound from the exact near-window chord estimate. -/
theorem point_step_lower (p : Parameters) (hstart : 0 < p.startIndex)
    (hsmall : p.scale 0 ≤ 1 / 4) (habove : ∀ k, 1 ≤ p.radius k) (k : ℕ) :
    nearSeparationConstant * p.scale (k / 2) ^ 2 ≤ ‖p.point (k + 1) - p.point k‖ := by
  have hpositive := nearWindow_pos p hstart hsmall k
  have hwindow : k + 1 - k ≤ nearWindow p k := by omega
  simpa only [Nat.add_sub_cancel_left, Nat.cast_one, mul_one] using
    near_point_separation p hstart habove k (k + 1) (Nat.lt_succ_self k) hwindow

/-- Helper for eq:polar-orders: the original quartic radius drop and quadratic
angle increment bound give the actual quadratic upper bound for one-step distance. -/
theorem point_step_upper {p : Parameters} {D : Fin 2 → ℝ} {K c B : ℝ}
    (h : RadiusEstimates p D K c B) (hstart : 0 < p.startIndex) (hB : 0 ≤ B) (k : ℕ) :
    ‖p.point (k + 1) - p.point k‖ ≤
      (B + Real.exp 1 * (2 * baseAngle)) * p.scale (k / 2) ^ 2 := by
  have hr : 0 ≤ p.radius k := zero_le_one.trans (h.above_one k).le
  have hradial : |p.radius (k + 1) - p.radius k| ≤ B * p.scale (k / 2) ^ 4 := by
    rw [abs_of_nonpos (sub_nonpos.mpr (h.strictAnti.antitone (Nat.le_succ k)))]
    linarith [(h.drop k).2]
  have hangle : |p.angle (k + 1) - p.angle k| ≤ (2 * baseAngle) * p.scale (k / 2) ^ 2 := by
    rw [abs_of_pos (sub_pos.mpr ((angle_strictMono p hstart) (Nat.lt_succ_self k)))]
    rw [← Parameters.angleIncrement_def]
    exact (angleIncrement_bounds p hstart k).2
  have hbound := polarChord_upper (p.radius (k + 1)) (p.radius k)
    (p.angle (k + 1)) (p.angle k) hr
  rw [← Parameters.point_def, ← Parameters.point_def] at hbound
  have hangleNonneg : 0 ≤ (2 * baseAngle) * p.scale (k / 2) ^ 2 := by
    have ha := baseAngle_pos
    positivity
  have ht := ScaleTails.scale_nonneg p (k / 2)
  have htone := ScaleTails.scale_le_one p hstart (k / 2)
  have hsquare := pow_le_one₀ ht htone (n := 2)
  have hfourth : p.scale (k / 2) ^ 4 ≤ p.scale (k / 2) ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg (p.scale (k / 2))) (sub_nonneg.mpr hsquare)]
  calc
    ‖p.point (k + 1) - p.point k‖ ≤
        |p.radius (k + 1) - p.radius k| + p.radius k * |p.angle (k + 1) - p.angle k| := hbound
    _ ≤ B * p.scale (k / 2) ^ 4 + p.radius k * ((2 * baseAngle) * p.scale (k / 2) ^ 2) :=
      add_le_add hradial (mul_le_mul_of_nonneg_left hangle hr)
    _ ≤ B * p.scale (k / 2) ^ 4 + Real.exp 1 * ((2 * baseAngle) * p.scale (k / 2) ^ 2) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right (h.upper k) hangleNonneg)
    _ ≤ B * p.scale (k / 2) ^ 2 + Real.exp 1 * ((2 * baseAngle) * p.scale (k / 2) ^ 2) :=
      add_le_add (mul_le_mul_of_nonneg_left hfourth hB) le_rfl
    _ = (B + Real.exp 1 * (2 * baseAngle)) * p.scale (k / 2) ^ 2 := by ring

/-- Helper for lem:polar-geometry: the Euclidean conclusions for the original
point sequence, separated from the already proved radius estimates. -/
structure PointEstimates (p : Parameters) (lower upper separation : ℝ) : Prop where
  /-- Helper for lem:polar-geometry: each actual point has its original radius as norm. -/
  norm : ∀ k, ‖p.point k‖ = p.radius k
  /-- Helper for eq:polar-chord: the exact chord identity for all actual point pairs. -/
  chord : ∀ k m, ‖p.point m - p.point k‖ ^ 2 = (p.radius m - p.radius k) ^ 2 +
    4 * p.radius m * p.radius k * Real.sin ((p.angle m - p.angle k) / 2) ^ 2
  /-- Helper for eq:polar-orders: the source two-sided quadratic one-step norm bounds. -/
  step : ∀ k, lower * p.scale (k / 2) ^ 2 ≤ ‖p.point (k + 1) - p.point k‖ ∧
    ‖p.point (k + 1) - p.point k‖ ≤ upper * p.scale (k / 2) ^ 2
  /-- Helper for lem:polar-geometry: precisely the unit circle is the cluster set. -/
  cluster : ∀ x, MapClusterPt x atTop p.point ↔ ‖x‖ = 1
  /-- Helper for eq:polar-separation: uniform separation for every distinct pair. -/
  separate : ∀ k m, k ≠ m → separation *
    max (p.scale (k / 2) ^ 2) (p.scale (m / 2) ^ 2) ≤ ‖p.point m - p.point k‖

/-- Helper for lem:polar-geometry: the source near/far and first-crossing arguments
turn the proved original radius estimates into actual point geometry. -/
theorem pointEstimatesOfRadiusEstimates {p : Parameters} {D : Fin 2 → ℝ} {K c B : ℝ}
    (h : RadiusEstimates p D K c B) (hstart : 0 < p.startIndex)
    (hsmall : p.scale 0 ≤ 1 / 4) (hc : 0 ≤ c) (hB : 0 ≤ B) :
    PointEstimates p nearSeparationConstant (B + Real.exp 1 * (2 * baseAngle))
      (min nearSeparationConstant (c / 128)) := by
  have habove (k : ℕ) : 1 ≤ p.radius k := (h.above_one k).le
  have hradius (k : ℕ) : 0 ≤ p.radius k := zero_le_one.trans (habove k)
  refine ⟨?_, point_chord_sq p, ?_, ?_, ?_⟩
  · intro k
    exact point_norm p k (hradius k)
  · intro k
    exact ⟨point_step_lower p hstart hsmall habove k, point_step_upper h hstart hB k⟩
  · exact point_cluster_iff p hstart hradius h.tendsto_one
  · exact point_separation p hstart hsmall habove h.strictAnti.antitone c hc
      (fun k ↦ (h.drop k).1)

/-- lem:polar-geometry and eq:polar-orders and eq:polar-separation: the original
actual points have the source radial expansion, quartic radial decrements, quadratic
step norms, exact unit-circle cluster set, and uniform all-pairs separation.
All positive constants precede every subsequently larger natural starting index. -/
theorem polarPointGeometry :
    ∃ η > 0, ∀ νStar ∈ Set.Ioo baseAngle (baseAngle + η),
      νStar ∈ TwoCycle.parameterSet ∧ ∃ K > 0, ∃ c > 0, ∃ B > 0,
        ∃ lower > 0, ∃ upper > 0, ∃ separation > 0, ∃ J : ℕ, 0 < J ∧
          ∀ j₀ ≥ J,
            RadiusEstimates (Parameters.of j₀ νStar)
                (RadiusExpansions.radiusCoefficient νStar) K c B ∧
              PointEstimates (Parameters.of j₀ νStar) lower upper separation := by
  obtain ⟨η, hη, hactual⟩ := polarRadiusProducts
  refine ⟨η, hη, ?_⟩
  intro νStar hnear
  obtain ⟨hparameter, K, hK, c, hc, B, hB, J₀, hJ₀, hradius⟩ := hactual νStar hnear
  have hquarter : (0 : ℝ) < 1 / 4 := by norm_num
  obtain ⟨J₁, _, hscale⟩ := Continuation.existsStartThreshold (1 / 4) hquarter
  have ha := baseAngle_pos
  have hupper : 0 < B + Real.exp 1 * (2 * baseAngle) := by positivity
  have hdenominator : (0 : ℝ) < 128 := by norm_num
  have hseparation : 0 < min nearSeparationConstant (c / 128) := by
    exact lt_min nearSeparationConstant_pos (div_pos hc hdenominator)
  refine ⟨hparameter, K, hK, c, hc, B, hB, nearSeparationConstant, nearSeparationConstant_pos,
    B + Real.exp 1 * (2 * baseAngle), hupper, min nearSeparationConstant (c / 128),
    hseparation, max J₀ J₁, hJ₀.trans_le (le_max_left _ _), ?_⟩
  intro j₀ hj₀
  have hj₀old := (le_max_left J₀ J₁).trans hj₀
  have hstart : 0 < (Parameters.of j₀ νStar).startIndex := by
    simpa only [Parameters.of_startIndex] using hJ₀.trans_le hj₀old
  have hsmall : (Parameters.of j₀ νStar).scale 0 ≤ 1 / 4 :=
    (hscale νStar j₀ ((le_max_right J₀ J₁).trans hj₀)).le
  have h := hradius j₀ hj₀old
  exact ⟨h, pointEstimatesOfRadiusEstimates h hstart hsmall hc.le hB.le⟩

/-- Helper for lem:polar-geometry: at the original consecutive cubic endpoints,
the polar directions agree exactly, so Euclidean distance equals radial decrease. -/
theorem point_cubic_distance (p : Parameters) (hanti : Antitone p.radius) (N : ℕ)
    (hstart : p.startIndex ≤ N ^ 3) :
    ‖p.point (2 * (N ^ 3 - p.startIndex)) -
        p.point (2 * ((N + 1) ^ 3 - p.startIndex))‖ =
      p.evenRadius (N ^ 3 - p.startIndex) - p.evenRadius ((N + 1) ^ 3 - p.startIndex) := by
  have hcubes : N ^ 3 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_left (Nat.le_succ N) 3
  have hnext : p.startIndex ≤ (N + 1) ^ 3 := hstart.trans hcubes
  have hindices : 2 * (N ^ 3 - p.startIndex) ≤ 2 * ((N + 1) ^ 3 - p.startIndex) :=
    Nat.mul_le_mul_left 2 (Nat.sub_le_sub_right hcubes p.startIndex)
  have hradial : 0 ≤ p.evenRadius (N ^ 3 - p.startIndex) -
      p.evenRadius ((N + 1) ^ 3 - p.startIndex) := by
    simpa only [Parameters.radius_even] using sub_nonneg.mpr (hanti hindices)
  simp only [Parameters.point_def, Parameters.angle_even, Parameters.radius_even,
    polarUnit_evenAngle_cubic p N hstart, polarUnit_evenAngle_cubic p (N + 1) hnext]
  rw [← sub_smul, norm_smul, polarUnit_norm, Real.norm_eq_abs, mul_one, abs_of_nonneg hradial]

/-- Helper for lem:polar-geometry: the source complete-turn radial asymptotic is
also an actual Euclidean distance estimate at the original cubic endpoints,
uniformly before all subsequently larger starting indices. -/
theorem polarPointFullTurn :
    ∃ η > 0, ∀ νStar ∈ Set.Ioo baseAngle (baseAngle + η),
      ∃ K > 0, ∃ J : ℕ, 0 < J ∧ ∀ j₀ ≥ J, ∀ N : ℕ, 0 < N → j₀ ≤ N ^ 3 →
        let p := Parameters.of j₀ νStar
        |‖p.point (2 * (N ^ 3 - j₀)) - p.point (2 * ((N + 1) ^ 3 - j₀))‖ -
            3 * (RadiusExpansions.radiusCoefficient νStar 0 +
              RadiusExpansions.radiusCoefficient νStar 1) / ((N : ℝ) * (N + 1))| ≤
          K * (N : ℝ) ^ (-3 : ℤ) := by
  obtain ⟨η₀, hη₀, hradii⟩ := polarRadiusProducts
  obtain ⟨η₁, hη₁, hturn⟩ := polarRadiusFullTurn
  refine ⟨min η₀ η₁, lt_min hη₀ hη₁, ?_⟩
  intro νStar hnear
  have hnear₀ : νStar ∈ Set.Ioo baseAngle (baseAngle + η₀) := by
    exact ⟨hnear.1, hnear.2.trans_le (add_le_add le_rfl (min_le_left _ _))⟩
  have hnear₁ : νStar ∈ Set.Ioo baseAngle (baseAngle + η₁) := by
    exact ⟨hnear.1, hnear.2.trans_le (add_le_add le_rfl (min_le_right _ _))⟩
  obtain ⟨_, K₀, _, c, _, B, _, J₀, hJ₀, hradius⟩ := hradii νStar hnear₀
  obtain ⟨K, hK, J₁, _, hbound⟩ := hturn νStar hnear₁
  refine ⟨K, hK, max J₀ J₁, hJ₀.trans_le (le_max_left _ _), ?_⟩
  intro j₀ hj₀ N hN hstart
  let p := Parameters.of j₀ νStar
  have hanti : Antitone p.radius :=
    (hradius j₀ ((le_max_left J₀ J₁).trans hj₀)).strictAnti.antitone
  have hstart' : p.startIndex ≤ N ^ 3 := by
    simpa only [p, Parameters.of_startIndex] using hstart
  have hdistance : ‖p.point (2 * (N ^ 3 - j₀)) - p.point (2 * ((N + 1) ^ 3 - j₀))‖ =
      p.evenRadius (N ^ 3 - j₀) - p.evenRadius ((N + 1) ^ 3 - j₀) := by
    simpa only [p, Parameters.of_startIndex] using point_cubic_distance p hanti N hstart'
  dsimp only
  rw [hdistance]
  exact hbound j₀ ((le_max_right J₀ J₁).trans hj₀) N hN hstart

end DFP.Polar.PointGeometry

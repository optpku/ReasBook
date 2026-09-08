module

public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusNormalForm
import all ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusNormalForm

public section

noncomputable section

namespace DFP.TwoLeg.Mixed

/-- The first residual pair along the independent-radius path has explicit value and
    derivative data at the zero-radius base point. -/
lemma independentRadiusFirstResiduals_hasDerivAt (θ : ℝ × ℝ × ℝ) :
    HasDerivAt (fun r ↦ independentRadiusFirstResiduals (θ, r))
      (θ.1 * (2 * θ.2.2 + θ.2.1 - 2), (-4 * θ.1, -2 * θ.1)) 0 := by
  let X : ℝ → ℝ := fun r ↦ r
  let b : ℝ → ℝ := fun _ ↦ θ.1
  let P : ℝ → ℝ := fun _ ↦ θ.2.1
  let J : ℝ → ℝ := fun _ ↦ θ.2.2
  let p : ℝ → ℝ := fun r ↦ 2 + P r * b r * X r
  let h : ℝ → ℝ := fun r ↦ 1 + J r * b r * X r
  let B : ℝ → ℝ := fun r ↦ 1 + 2 * b r * X r + X r ^ 2
  let C : ℝ → ℝ := fun r ↦ (1 + b r * X r) ^ 2 +
    p r * X r ^ 2 * (b r + X r) ^ 2
  let a : ℝ → ℝ := fun r ↦ h r * p r -
    h r * p r ^ 2 * X r ^ 2 * (b r + X r) ^ 2 / C r + 1 / B r
  let c : ℝ → ℝ := fun r ↦ 1 / B r -
    h r * p r * X r * (b r + X r) * (1 + b r * X r) / C r
  let d : ℝ → ℝ := fun r ↦ h r - h r * (1 + b r * X r) ^ 2 / C r + 1 / B r
  have hX : HasDerivAt X 1 0 := by
    change HasDerivAt id 1 0
    exact hasDerivAt_id 0
  have hb : HasDerivAt b 0 0 := by
    simpa [b] using hasDerivAt_const (x := (0 : ℝ)) θ.1
  have hP : HasDerivAt P 0 0 := by
    simpa [P] using hasDerivAt_const (x := (0 : ℝ)) θ.2.1
  have hJ : HasDerivAt J 0 0 := by
    simpa [J] using hasDerivAt_const (x := (0 : ℝ)) θ.2.2
  have hp : HasDerivAt p (θ.1 * θ.2.1) 0 := by
    have h := ((hP.mul hb).mul hX).const_add 2
    apply h.congr_deriv
    · simp [p, P, b, X]
      ring
  have hh : HasDerivAt h (θ.1 * θ.2.2) 0 := by
    have h' := ((hJ.mul hb).mul hX).const_add 1
    apply h'.congr_deriv
    · simp [h, J, b, X]
      ring
  have hB : HasDerivAt B (2 * θ.1) 0 := by
    have h' := ((hb.mul hX).const_mul 2).add (hX.pow 2) |>.const_add 1
    have h'' : HasDerivAt
        (fun x : ℝ ↦ 1 + ((fun y : ℝ ↦ 2 * (b * X) y) + X ^ 2) x)
        (2 * θ.1) 0 := by
      apply h'.congr_deriv
      simp [b, X]
    have hfun : (fun x ↦ 1 + ((fun y ↦ 2 * (b * X) y) + X ^ 2) x) = B := by
      funext r
      simp [B]
      ring
    rw [hfun] at h''
    exact h''
  have hC : HasDerivAt C (2 * θ.1) 0 := by
    have h' := ((hb.mul hX).const_add 1).pow 2 |>.add
      ((hp.mul (hX.pow 2)).mul ((hb.add hX).pow 2))
    apply h'.congr_deriv
    · simp [C, b, X, p, P]
  have hB0 : B 0 ≠ 0 := by simp [B, b, X]
  have hC0 : C 0 ≠ 0 := by simp [C, b, X, p, P]
  have ha : HasDerivAt a (θ.1 * (2 * θ.2.2 + θ.2.1 - 2)) 0 := by
    have h' := (hh.mul hp).sub
      (((((hh.mul (hp.pow 2)).mul (hX.pow 2)).mul ((hb.add hX).pow 2)).div hC hC0)) |>.add
      ((hasDerivAt_const (x := (0 : ℝ)) (c := (1 : ℝ))).div hB hB0)
    apply h'.congr_deriv
    · simp [a, b, P, J, X, p, h, B, C]
      ring
  have hc : HasDerivAt c (-4 * θ.1) 0 := by
    have h' := (hasDerivAt_const (x := (0 : ℝ)) (c := (1 : ℝ))).div hB hB0 |>.sub
      (((((hh.mul hp).mul hX).mul (hb.add hX)).mul
        ((hb.mul hX).const_add 1)).div hC hC0)
    apply h'.congr_deriv
    · simp [c, b, P, J, X, p, h, B, C]
      ring
  have hd : HasDerivAt d (-2 * θ.1) 0 := by
    have hterm := (hh.mul (((hb.mul hX).const_add 1).pow 2)).div hC hC0
    have h' := hh.sub hterm |>.add
      ((hasDerivAt_const (x := (0 : ℝ)) (c := (1 : ℝ))).div hB hB0)
    apply h'.congr_deriv
    · simp [d, b, P, J, X, p, h, B, C]
  have hpair := ha.prodMk (hc.prodMk hd)
  apply hpair.congr_of_eventuallyEq
  have hpairEq : ∀ r : ℝ,
      independentRadiusFirstResiduals (θ, r) = (a r, (c r, d r)) := by
    intro r
    simp [independentRadiusFirstResiduals, independentFirstResiduals,
      a, c, d, b, P, J, p, h, B, C, X]
  exact Filter.Eventually.of_forall hpairEq

/-- The first gradient residual pair along the independent-radius path has explicit
    first-order data at zero radius. -/
lemma independentRadiusFirstGradientResiduals_hasDerivAt (θ : ℝ × ℝ × ℝ) :
    HasDerivAt (fun r ↦ independentRadiusFirstGradientResiduals (θ, r))
      (-2 * θ.1, θ.1 * (θ.2.1 + 6) / 3) 0 := by
  let X : ℝ → ℝ := fun r ↦ r
  let b : ℝ → ℝ := fun _ ↦ θ.1
  let P : ℝ → ℝ := fun _ ↦ θ.2.1
  let p : ℝ → ℝ := fun r ↦ 2 + P r * b r * X r
  let B : ℝ → ℝ := fun r ↦ 1 + 2 * b r * X r + X r ^ 2
  let q : ℝ → ℝ := fun r ↦ 1 -
    2 * (p r + 1) * X r * (b r + X r) / (3 * B r)
  let u : ℝ → ℝ := fun r ↦ p r -
    2 * (p r + 1) * (1 + b r * X r) / (3 * B r)
  have hX : HasDerivAt X 1 0 := by
    change HasDerivAt id 1 0
    exact hasDerivAt_id 0
  have hb : HasDerivAt b 0 0 := by
    simpa [b] using hasDerivAt_const (x := (0 : ℝ)) θ.1
  have hP : HasDerivAt P 0 0 := by
    simpa [P] using hasDerivAt_const (x := (0 : ℝ)) θ.2.1
  have hp : HasDerivAt p (θ.1 * θ.2.1) 0 := by
    have h' := ((hP.mul hb).mul hX).const_add 2
    apply h'.congr_deriv
    · simp [p, P, b, X]
      ring
  have hB : HasDerivAt B (2 * θ.1) 0 := by
    have h' := ((hb.mul hX).const_mul 2).add (hX.pow 2) |>.const_add 1
    have h'' : HasDerivAt
        (fun x : ℝ ↦ 1 + ((fun y : ℝ ↦ 2 * (b * X) y) + X ^ 2) x)
        (2 * θ.1) 0 := by
      apply h'.congr_deriv
      simp [b, X]
    have hfun : (fun x ↦ 1 + ((fun y ↦ 2 * (b * X) y) + X ^ 2) x) = B := by
      funext r
      simp [B]
      ring
    rw [hfun] at h''
    exact h''
  have hq : HasDerivAt q (-2 * θ.1) 0 := by
    have hdenRaw := (hasDerivAt_const (x := (0 : ℝ)) (c := (3 : ℝ))).mul hB
    have hdenRaw' : HasDerivAt
        ((fun x : ℝ ↦ (3 : ℝ)) * B) (6 * θ.1) 0 := by
      apply hdenRaw.congr_deriv
      simp
      ring
    have hdenEq : ∀ r : ℝ, (fun x : ℝ ↦ (3 : ℝ) * B x) r =
        ((fun x : ℝ ↦ (3 : ℝ)) * B) r := by
      intro r
      simp
    have hden : HasDerivAt (fun r ↦ (3 : ℝ) * B r) (6 * θ.1) 0 := by
      exact hdenRaw'.congr_of_eventuallyEq (Filter.Eventually.of_forall hdenEq)
    have hden0 : (fun r ↦ (3 : ℝ) * B r) 0 ≠ 0 := by norm_num [B, b, X]
    have hnum := (((hp.add (hasDerivAt_const (x := (0 : ℝ)) (c := (1 : ℝ)))).mul hX).mul
        (hb.add hX)).const_mul 2
    have h' := (hasDerivAt_const (x := (0 : ℝ)) (c := (1 : ℝ))).sub (hnum.div hden hden0)
    have htemp : HasDerivAt
        ((fun x : ℝ ↦ (1 : ℝ)) -
          (fun y : ℝ ↦
            2 * ((p + (fun x : ℝ ↦ (1 : ℝ))) * X * (b + X)) y) /
            (fun r : ℝ ↦ 3 * B r))
        (-2 * θ.1) 0 := by
      apply h'.congr_deriv
      simp [p, B, b, P, X]
      ring
    have hfun :
        ((fun x : ℝ ↦ (1 : ℝ)) -
          (fun y : ℝ ↦
            2 * ((p + (fun x : ℝ ↦ (1 : ℝ))) * X * (b + X)) y) /
            (fun r : ℝ ↦ 3 * B r)) =
          (fun r : ℝ ↦
            1 - 2 * (p r + 1) * X r * (b r + X r) / (3 * B r)) := by
      funext r
      simp
      ring
    rw [hfun] at htemp
    simpa [q] using htemp
  have hu : HasDerivAt u (θ.1 * (θ.2.1 + 6) / 3) 0 := by
    have hdenRaw := (hasDerivAt_const (x := (0 : ℝ)) (c := (3 : ℝ))).mul hB
    have hdenRaw' : HasDerivAt
        ((fun x : ℝ ↦ (3 : ℝ)) * B) (6 * θ.1) 0 := by
      apply hdenRaw.congr_deriv
      simp
      ring
    have hdenEq : ∀ r : ℝ, (fun x : ℝ ↦ (3 : ℝ) * B x) r =
        ((fun x : ℝ ↦ (3 : ℝ)) * B) r := by
      intro r
      simp
    have hden : HasDerivAt (fun r ↦ (3 : ℝ) * B r) (6 * θ.1) 0 := by
      exact hdenRaw'.congr_of_eventuallyEq (Filter.Eventually.of_forall hdenEq)
    have hden0 : (fun r ↦ (3 : ℝ) * B r) 0 ≠ 0 := by norm_num [B, b, X]
    have hnum := ((hp.add (hasDerivAt_const (x := (0 : ℝ)) (c := (1 : ℝ)))).mul
        ((hb.mul hX).const_add 1)).const_mul 2
    have h' := hp.sub (hnum.div hden hden0)
    have htemp : HasDerivAt
        (p -
          (fun y : ℝ ↦
            2 * ((p + (fun x : ℝ ↦ (1 : ℝ))) *
              (fun x : ℝ ↦ 1 + (b * X) x)) y) /
            (fun r : ℝ ↦ 3 * B r))
        (θ.1 * (θ.2.1 + 6) / 3) 0 := by
      apply h'.congr_deriv
      simp [p, B, b, P, X]
      ring
    have hfun :
        (p -
          (fun y : ℝ ↦
            2 * ((p + (fun x : ℝ ↦ (1 : ℝ))) *
              (fun x : ℝ ↦ 1 + (b * X) x)) y) /
            (fun r : ℝ ↦ 3 * B r)) =
          (fun r : ℝ ↦
            p r - 2 * (p r + 1) * (1 + b r * X r) / (3 * B r)) := by
      funext r
      simp
      ring
    rw [hfun] at htemp
    simpa [u] using htemp
  have hpair := hq.prodMk hu
  apply hpair.congr_of_eventuallyEq
  have hpairEq : ∀ r : ℝ,
      independentRadiusFirstGradientResiduals (θ, r) = (q r, u r) := by
    intro r
    simp [independentRadiusFirstGradientResiduals, independentFirstGradientResiduals,
      q, u, b, P, p, B, X]
  exact Filter.Eventually.of_forall hpairEq

end DFP.TwoLeg.Mixed

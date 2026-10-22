/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section23_part1

open scoped Topology

section Chap05
section Section23

/-- Helper for Theorem 23.1: real epigraph heights for the upper directional derivative are
stable under convex combinations of directions. -/
lemma helperForTheorem_23_1_upperDerivative_epigraph_convex {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (hf : ConvexFunction f) (x : Fin n → ℝ)
    (hx : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal))
    (y₁ y₂ : Fin n → ℝ) {s μ ν : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hμ : upperDirectionalDerivativeAt f x y₁ ≤ (μ : EReal))
    (hν : upperDirectionalDerivativeAt f x y₂ ≤ (ν : EReal)) :
    upperDirectionalDerivativeAt f x ((1 - s) • y₁ + s • y₂) ≤
      ((((1 - s) * μ + s * ν : ℝ)) : EReal) := by
  let D : (Fin n → ℝ) → EReal := upperDirectionalDerivativeAt f x
  let mix : Fin n → ℝ := (1 - s) • y₁ + s • y₂
  have hmono₁ := helperForTheorem_23_1_differenceQuotient_monotone f hf x y₁ hx
  have hmono₂ := helperForTheorem_23_1_differenceQuotient_monotone f hf x y₂ hx
  have hmonoMix := helperForTheorem_23_1_differenceQuotient_monotone f hf x mix hx
  -- Route correction: we contradict a real height strictly below the mixed derivative by forcing
  -- one common positive step where the mixed quotient already lies below that height.
  by_contra hcontra
  have hcomb_lt :
      ((((1 - s) * μ + s * ν : ℝ)) : EReal) < D mix := by
    exact lt_of_not_ge hcontra
  obtain ⟨ρ, hcombρ, hρmix⟩ := EReal.exists_between_coe_real hcomb_lt
  let ε : ℝ := (ρ - ((1 - s) * μ + s * ν)) / 2
  have hcombρ_real : ((1 - s) * μ + s * ν) < ρ := by
    exact (EReal.coe_lt_coe_iff).1 hcombρ
  have hεpos : 0 < ε := by
    dsimp [ε]
    linarith
  have hy₁_lt : D y₁ < ((μ + ε : ℝ) : EReal) := by
    refine lt_of_le_of_lt hμ ?_
    exact (EReal.coe_lt_coe_iff).2 (by linarith)
  have hy₂_lt : D y₂ < ((ν + ε : ℝ) : EReal) := by
    refine lt_of_le_of_lt hν ?_
    exact (EReal.coe_lt_coe_iff).2 (by linarith)
  rcases helperForTheorem_23_1_commonPositiveStep_below_real_bounds f x y₁ y₂
      hmono₁ hmono₂ hy₁_lt hy₂_lt with ⟨t, ht, hq₁, hq₂⟩
  have hqMix :
      directionalDifferenceQuotientAt f x mix t ≤
        ((((1 - s) * (μ + ε) + s * (ν + ε) : ℝ)) : EReal) :=
    helperForTheorem_23_1_pointwiseDifferenceQuotient_convexCombination_realBound
      f hf x y₁ y₂ hx hs0 hs1 ht (le_of_lt hq₁) (le_of_lt hq₂)
  have hslack_real : (1 - s) * (μ + ε) + s * (ν + ε) < ρ := by
    dsimp [ε]
    ring_nf
    linarith
  have hqMix_ltρ : directionalDifferenceQuotientAt f x mix t < (ρ : EReal) := by
    exact lt_of_le_of_lt hqMix ((EReal.coe_lt_coe_iff).2 hslack_real)
  have hQmix_bdd :
      BddBelow ((Set.Ioi (0 : ℝ)).image fun u : ℝ => directionalDifferenceQuotientAt f x mix u) := by
    refine ⟨⊥, ?_⟩
    intro z hz
    simp at hz ⊢
  have hDmix_le_q :
      D mix ≤ directionalDifferenceQuotientAt f x mix t := by
    change upperDirectionalDerivativeAt f x mix ≤ directionalDifferenceQuotientAt f x mix t
    rw [helperForTheorem_23_1_upperDerivative_eq_sInf_differenceQuotients f x mix hmonoMix]
    exact csInf_le hQmix_bdd (by exact ⟨t, ht, rfl⟩)
  exact (not_lt_of_ge (le_trans (le_of_lt hρmix) hDmix_le_q)) hqMix_ltρ

/-- Helper for Theorem 23.1: strict real upper bounds on the derivative in opposite directions
must have nonnegative midpoint. -/
lemma helperForTheorem_23_1_midpoint_real_bound {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (hf : ConvexFunction f) (x : Fin n → ℝ)
    (hx : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal))
    (y : Fin n → ℝ) {μ ν : ℝ}
    (hμ : upperDirectionalDerivativeAt f x y < (μ : EReal))
    (hν : upperDirectionalDerivativeAt f x (-y) < (ν : EReal)) :
    0 ≤ (μ + ν) / 2 := by
  have hmono_y := helperForTheorem_23_1_differenceQuotient_monotone f hf x y hx
  have hmono_neg := helperForTheorem_23_1_differenceQuotient_monotone f hf x (-y) hx
  rcases helperForTheorem_23_1_commonPositiveStep_below_real_bounds f x y (-y)
      hmono_y hmono_neg hμ hν with ⟨t, ht, hq_y, hq_neg⟩
  have hmix :
      ((1 - (1 / 2 : ℝ)) • y + (1 / 2 : ℝ) • (-y)) = (0 : Fin n → ℝ) := by
    ext i
    simp [smul_eq_mul]
    ring
  have hmixNeg :
      ((1 - (1 / 2 : ℝ)) • y + -((1 / 2 : ℝ) • y)) = (0 : Fin n → ℝ) := by
    simpa [smul_neg] using hmix
  have hqZeroRaw :
      directionalDifferenceQuotientAt f x (((1 - (1 / 2 : ℝ)) • y + (1 / 2 : ℝ) • (-y)) : Fin n → ℝ) t ≤
        ((((1 - (1 / 2 : ℝ)) * μ + (1 / 2 : ℝ) * ν : ℝ)) : EReal) :=
    helperForTheorem_23_1_pointwiseDifferenceQuotient_convexCombination_realBound
      (s := (1 / 2 : ℝ)) f hf x y (-y) hx (by norm_num) (by norm_num) ht
      (le_of_lt hq_y) (le_of_lt hq_neg)
  have hqZero :
      directionalDifferenceQuotientAt f x 0 t ≤ ((((1 - (1 / 2 : ℝ)) * μ + (1 / 2 : ℝ) * ν : ℝ)) : EReal) := by
    rw [show (((1 - (1 / 2 : ℝ)) • y + (1 / 2 : ℝ) • (-y)) : Fin n → ℝ) =
        ((1 - (1 / 2 : ℝ)) • y + -((1 / 2 : ℝ) • y)) by simp [smul_neg]] at hqZeroRaw
    rw [hmixNeg] at hqZeroRaw
    exact hqZeroRaw
  have hzeroQuot :
      directionalDifferenceQuotientAt f x 0 t = 0 := by
    rw [directionalDifferenceQuotientAt]
    simp [EReal.sub_self hx.1 hx.2]
  have hmidCoeff :
      (1 - (1 / 2 : ℝ)) * μ + (1 / 2 : ℝ) * ν = (μ + ν) / 2 := by
    ring
  have hmidCoeffE :
      ((((1 - (1 / 2 : ℝ)) * μ + (1 / 2 : ℝ) * ν : ℝ)) : EReal) =
        (((μ + ν) / 2 : ℝ) : EReal) := by
    exact congrArg (fun r : ℝ => ((r : ℝ) : EReal)) hmidCoeff
  have hmidE : (0 : EReal) ≤ (((μ + ν) / 2 : ℝ) : EReal) := by
    calc
      (0 : EReal) = directionalDifferenceQuotientAt f x 0 t := by
        symm
        exact hzeroQuot
      _ ≤ ((((1 - (1 / 2 : ℝ)) * μ + (1 / 2 : ℝ) * ν : ℝ)) : EReal) := hqZero
      _ = (((μ + ν) / 2 : ℝ) : EReal) := hmidCoeffE
  have hmidE' : ((0 : ℝ) : EReal) ≤ (((μ + ν) / 2 : ℝ) : EReal) := by
    simpa using hmidE
  have hmidReal : (0 : ℝ) ≤ (μ + ν) / 2 := (EReal.coe_le_coe_iff).1 hmidE'
  exact hmidReal

/-- Theorem 23.1: If `f` is convex and finite-valued at `x`, then for every direction `y` the
right directional difference quotient `λ ↦ (f (x + λ • y) - f x) / λ` is nondecreasing on
`(0, ∞)`, hence the directional derivative exists as the limit of these quotients and equals their
infimum over `λ > 0`. Moreover, the map `y ↦ f'(x;y)` is a positively homogeneous convex function,
it satisfies `f'(x;0) = 0`, and `-f'(x;-y) ≤ f'(x;y)` for every `y`. -/
theorem convex_directionalDerivative_monotone_exists_and_sublinear {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (hf : ConvexFunction f) (x : Fin n → ℝ)
    (hx : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal)) :
    (∀ y : Fin n → ℝ,
      MonotoneOn (directionalDifferenceQuotientAt f x y) (Set.Ioi (0 : ℝ)) ∧
      Filter.Tendsto (directionalDifferenceQuotientAt f x y) (𝓝[>] (0 : ℝ))
        (𝓝 (upperDirectionalDerivativeAt f x y)) ∧
      upperDirectionalDerivativeAt f x y =
        sInf ((Set.Ioi (0 : ℝ)).image fun t : ℝ => directionalDifferenceQuotientAt f x y t)) ∧
    PositivelyHomogeneous (upperDirectionalDerivativeAt f x) ∧
    ConvexFunction (upperDirectionalDerivativeAt f x) ∧
    upperDirectionalDerivativeAt f x 0 = 0 ∧
    ∀ y : Fin n → ℝ, -(upperDirectionalDerivativeAt f x (-y)) ≤ upperDirectionalDerivativeAt f x y := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro y
    refine ⟨?_, ?_, ?_⟩
    · -- The first component is the secant-slope monotonicity along the ray.
      exact helperForTheorem_23_1_differenceQuotient_monotone f hf x y hx
    · -- The monotone quotient family converges to its infimum.
      exact helperForTheorem_23_1_tendsto_upperDerivative f x y
        (helperForTheorem_23_1_differenceQuotient_monotone f hf x y hx)
    · -- The upper derivative agrees with the infimum of the positive quotients.
      exact helperForTheorem_23_1_upperDerivative_eq_sInf_differenceQuotients f x y
        (helperForTheorem_23_1_differenceQuotient_monotone f hf x y hx)
  · -- Route correction: prove positive homogeneity by a direct `sInf` comparison on rescaled
    -- quotients, rather than by revisiting the unstable derivative-level limit route.
    exact helperForTheorem_23_1_upperDerivative_posHom_direct f hf x hx
  · -- Route correction: prove convexity via real-height epigraph points and one common positive
    -- step, which keeps the contradiction entirely in the finite real layer.
    have hconvEpigraph :
        Convex ℝ (epigraph (Set.univ : Set (Fin n → ℝ)) (upperDirectionalDerivativeAt f x)) := by
      intro p hp q hq a b ha hb hab
      have hbp1 : b ≤ 1 := by
        linarith
      have haeq : a = 1 - b := by
        linarith
      have hp' : upperDirectionalDerivativeAt f x p.1 ≤ (p.2 : EReal) := by
        simpa [epigraph] using hp.2
      have hq' : upperDirectionalDerivativeAt f x q.1 ≤ (q.2 : EReal) := by
        simpa [epigraph] using hq.2
      have hmix :
          upperDirectionalDerivativeAt f x ((1 - b) • p.1 + b • q.1) ≤
            ((((1 - b) * p.2 + b * q.2 : ℝ)) : EReal) :=
        helperForTheorem_23_1_upperDerivative_epigraph_convex f hf x hx p.1 q.1 hb hbp1 hp' hq'
      have hmem :
          (((1 - b) • p.1 + b • q.1), ((1 - b) * p.2 + b * q.2)) ∈
            epigraph (Set.univ : Set (Fin n → ℝ)) (upperDirectionalDerivativeAt f x) := by
        exact epigraph_mem_of_le_aux (S := (Set.univ : Set (Fin n → ℝ)))
          (x := (1 - b) • p.1 + b • q.1) (μ := (1 - b) * p.2 + b * q.2) (by simp) hmix
      convert hmem using 1
      ext <;> simp [haeq, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
    simpa [ConvexFunction] using hconvEpigraph
  · -- The zero direction gives the constant zero quotient family.
    exact helperForTheorem_23_1_upperDerivative_zero f x hx
  · -- Route correction: extract a real separator between `D y` and `-D (-y)`, then contradict the
    -- midpoint bound for real upper estimates in opposite directions.
    intro y
    let D : (Fin n → ℝ) → EReal := upperDirectionalDerivativeAt f x
    by_contra hneg
    have hlt : D y < -(D (-y)) := by
      exact lt_of_not_ge hneg
    obtain ⟨μ, hDyμ, hμneg⟩ := EReal.exists_between_coe_real hlt
    have hDneg_lt :
        D (-y) < ((-μ : ℝ) : EReal) := by
      by_cases htop : D (-y) = (⊤ : EReal)
      · simpa [D, htop] using hμneg
      · by_cases hbot : D (-y) = (⊥ : EReal)
        · simpa [D, hbot] using (EReal.bot_lt_coe (-μ))
        · have hμneg' :
            (μ : EReal) < (((-(D (-y)).toReal : ℝ)) : EReal) := by
            have hnegcoe : -D (-y) = (((-(D (-y)).toReal : ℝ)) : EReal) := by
              rw [← EReal.coe_toReal htop hbot]
              simp
            simpa [hnegcoe] using hμneg
          have hμreal : μ < -(D (-y)).toReal := by
            exact (EReal.coe_lt_coe_iff).1 hμneg'
          have hnegreal : (D (-y)).toReal < -μ := by
            linarith
          have hcoe : (((D (-y)).toReal : ℝ) : EReal) = D (-y) := EReal.coe_toReal htop hbot
          have hnegrealE : (((D (-y)).toReal : ℝ) : EReal) < ((-μ : ℝ) : EReal) := by
            exact (EReal.coe_lt_coe_iff).2 hnegreal
          rw [← hcoe]
          exact hnegrealE
    obtain ⟨ν, hDnegν, hνlt⟩ := EReal.exists_between_coe_real hDneg_lt
    have hmid_nonneg :
        0 ≤ (μ + ν) / 2 :=
      helperForTheorem_23_1_midpoint_real_bound f hf x hx y hDyμ hDnegν
    have hνlt_real : ν < -μ := by
      exact (EReal.coe_lt_coe_iff).1 hνlt
    have hmid_neg : (μ + ν) / 2 < 0 := by
      linarith
    exact (not_lt_of_ge hmid_nonneg) hmid_neg

end Section23
end Chap05

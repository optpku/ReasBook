/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap18.Example_18_16
import Books.ProbabilityTheory_Klenke_2020.Items.Chap18.Definition_18_17

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators ENNReal

noncomputable section

universe u

namespace ProbabilityTheory

variable {Λ : Type u} [Fintype Λ] [DecidableEq Λ]

/-- The neighbor-interaction sum
`∑_{j : j ∼ i} (1_{x(j) ≠ σ} - 1 / 2)` appearing in the single-site Ising conditional law. -/
def isingNeighborBias (G : SimpleGraph Λ) [DecidableRel G.Adj]
    (x : ising_configuration Λ) (i : Λ) (σ : ising_spin) : ℝ :=
  ∑ j, if G.Adj i j then ((if x j ≠ σ then (1 : ℝ) else 0) - (1 / 2 : ℝ)) else 0

/-- The single-site conditional probability of resetting the spin at `i` to `σ` in the finite
Ising model with inverse temperature `β`. -/
def isingConditionalProbability (β : ℝ) (G : SimpleGraph Λ) [DecidableRel G.Adj]
    (x : ising_configuration Λ) (i : Λ) (σ : ising_spin) : ℝ :=
  (1 + Real.exp (2 * β * isingNeighborBias G x i σ))⁻¹

omit [DecidableEq Λ] in
/-- The single-site Ising conditional law is the logistic expression determined by the neighboring
spins. -/
theorem isingConditionalProbability_eq_logistic
    (β : ℝ) (G : SimpleGraph Λ) [DecidableRel G.Adj]
    (x : ising_configuration Λ) (i : Λ) (σ : ising_spin) :
    isingConditionalProbability β G x i σ =
      (1 + Real.exp (2 * β * ∑ j, if G.Adj i j then
        ((if x j ≠ σ then (1 : ℝ) else 0) - (1 / 2 : ℝ)) else 0))⁻¹ :=
  rfl

private def positiveIsingSpin : ising_spin :=
  ⟨1, by decide⟩

omit [DecidableEq Λ] in
private theorem isingBoltzmannPMF_tsum_ne_zero
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (β : ℝ) :
    (∑' x : ising_configuration Λ, ising_boltzmann_weight G β x) ≠ 0 := by
  classical
  let x : ising_configuration Λ := fun _ ↦ positiveIsingSpin
  have hx : ising_boltzmann_weight G β x ≠ 0 := by
    simp [ising_boltzmann_weight, ENNReal.ofReal_eq_zero, Real.exp_pos]
  have hle : ising_boltzmann_weight G β x ≤
      ∑' y : ising_configuration Λ, ising_boltzmann_weight G β y := by
    simpa [tsum_fintype] using
      Finset.single_le_sum (fun y hy ↦ bot_le) (Finset.mem_univ x)
  intro hsum
  exact hx (le_antisymm (hsum ▸ hle) bot_le)

omit [DecidableEq Λ] in
private theorem isingBoltzmannPMF_tsum_ne_top
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (β : ℝ) :
    (∑' x : ising_configuration Λ, ising_boltzmann_weight G β x) ≠ ∞ := by
  classical
  simpa [tsum_fintype] using
    (ENNReal.sum_ne_top.2 fun x hx ↦ by simp [ising_boltzmann_weight] :
      ∑ x ∈ (Finset.univ : Finset (ising_configuration Λ)), ising_boltzmann_weight G β x ≠
        ∞)

/-- The finite Ising Boltzmann distribution at inverse temperature `β`, obtained by normalizing
the Boltzmann weight `x ↦ exp (-β H(x))`. -/
def isingBoltzmannPMF
    (G : SimpleGraph Λ) [DecidableRel G.Adj] (β : ℝ) : PMF (ising_configuration Λ) :=
  PMF.normalize (ising_boltzmann_weight G β)
    (isingBoltzmannPMF_tsum_ne_zero G β)
    (isingBoltzmannPMF_tsum_ne_top G β)

section GibbsSampler

variable [Nonempty Λ]
variable (β : ℝ) (G : SimpleGraph Λ) [DecidableRel G.Adj]

omit [Nonempty Λ] [DecidableEq Λ] in
private theorem isingBoltzmannPMF_apply_ne_zero (x : ising_configuration Λ) :
    isingBoltzmannPMF G β x ≠ 0 := by
  rw [isingBoltzmannPMF, PMF.normalize_apply]
  refine mul_ne_zero ?_ ?_
  · simp [ising_boltzmann_weight, ENNReal.ofReal_eq_zero, Real.exp_pos]
  · simp [ENNReal.inv_eq_zero, isingBoltzmannPMF_tsum_ne_top G β]

omit [Nonempty Λ] [DecidableEq Λ] in
private theorem isingBoltzmannPMF_hasPositiveGibbsCoordinateMarginals :
    HasPositiveGibbsCoordinateMarginals (isingBoltzmannPMF G β) := by
  apply hasPositiveGibbsCoordinateMarginals_of_apply_ne_zero
  intro x
  exact isingBoltzmannPMF_apply_ne_zero β G x

/-- Helper for Example 18.18: every Ising spin is either `1` or `-1`. -/
private lemma isingSpin_eq_one_or_eq_neg_one (σ : ising_spin) : σ.1 = 1 ∨ σ.1 = -1 := by
  -- The excluded middle branch `σ.1 = 0` is ruled out by the Ising-spin subtype condition.
  rcases SignType.trichotomy σ.1 with hneg | hzero | hpos
  · exact Or.inr hneg
  · exact False.elim (σ.2 hzero)
  · exact Or.inl hpos

/-- Helper for Example 18.18: on the two-point Ising-spin space, being different from
`flip_spin σ` is equivalent to being equal to `σ`. -/
private lemma ne_flipSpin_iff_eq {σ τ : ising_spin} : τ ≠ flip_spin σ ↔ τ = σ := by
  -- Reduce both spins to the concrete values `1` and `-1`, then simplify the subtype equality.
  rcases isingSpin_eq_one_or_eq_neg_one σ with hσ | hσ <;>
    rcases isingSpin_eq_one_or_eq_neg_one τ with hτ | hτ <;>
    simp [flip_spin, hσ, hτ, Subtype.ext_iff]

/-- Helper for Example 18.18: flipping an Ising spin never fixes it. -/
private lemma flipSpin_ne_self (σ : ising_spin) : flip_spin σ ≠ σ := by
  -- The two Ising spins are `1` and `-1`, so negation swaps them.
  rcases isingSpin_eq_one_or_eq_neg_one σ with hσ | hσ <;>
    simp [flip_spin, hσ, Subtype.ext_iff]

/-- Helper for Example 18.18: every Ising spin is either `σ` or `flip_spin σ`. -/
private lemma eq_or_eq_flipSpin (σ τ : ising_spin) : τ = σ ∨ τ = flip_spin σ := by
  -- There are only two Ising spins, so excluding `σ` forces the flipped value.
  by_cases hτ : τ = σ
  · exact Or.inl hτ
  · right
    by_contra hflip
    exact hτ ((ne_flipSpin_iff_eq (σ := σ) (τ := τ)).mp hflip)

/-- Helper for Example 18.18: summing over `ising_spin` is the same as summing over the pair
`σ, flip_spin σ`. -/
private lemma sum_isingSpin_eq_self_add_flip {α : Type*} [AddCommMonoid α]
    (f : ising_spin → α) (σ : ising_spin) :
    ∑ τ : ising_spin, f τ = f σ + f (flip_spin σ) := by
  classical
  have huniv : (Finset.univ : Finset ising_spin) = {σ, flip_spin σ} := by
    -- Membership in `Finset.univ` is equivalent to being one of the two Ising spins.
    ext τ
    simp [eq_or_eq_flipSpin (σ := σ) (τ := τ)]
  rw [huniv, Finset.sum_insert]
  · simp
  · simpa [eq_comm] using flipSpin_ne_self σ

omit [Fintype Λ] [Nonempty Λ] in
/-- Helper for Example 18.18: flipping the updated configuration at `i` is the same as replacing
that coordinate by the flipped spin. -/
private lemma flipAt_gibbsCoordinateReplace_eq
    (x : ising_configuration Λ) (i : Λ) (σ : ising_spin) :
    flip_at (gibbsCoordinateReplace x i σ) i = gibbsCoordinateReplace x i (flip_spin σ) := by
  -- Both single-site update operations agree away from `i` and send `i` to `flip_spin σ`.
  ext j
  by_cases hji : j = i
  · subst hji
    simp [flip_at]
  · simp [flip_at, hji]

omit [DecidableEq Λ] in
/-- Helper for Example 18.18: the energy difference between the two Ising configurations in one
Gibbs fiber is `2 * isingNeighborBias G x i σ`. -/
private lemma hamiltonian_replace_difference_eq_neighborBias
    (x : ising_configuration Λ) (i : Λ) (σ : ising_spin) :
    hamiltonian G (gibbsCoordinateReplace x i σ) -
      hamiltonian G (gibbsCoordinateReplace x i (flip_spin σ)) =
        2 * isingNeighborBias G x i σ := by
  classical
  have hflip :=
    hamiltonian_flip_difference_eq
      (G := G) (x := gibbsCoordinateReplace x i σ) (i := i)
  rw [flipAt_gibbsCoordinateReplace_eq (x := x) (i := i) (σ := σ)] at hflip
  have hbias :
      ∑ j,
        (if G.Adj j i then
          ((if gibbsCoordinateReplace x i σ j ≠ gibbsCoordinateReplace x i σ i then
              (1 : ℝ)
            else 0) - (1 / 2 : ℝ))
        else 0)
        = isingNeighborBias G x i σ := by
    -- Away from `i`, the update matches `x`, and the diagonal term vanishes.
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    by_cases hji : j = i
    · subst hji
      simp
    · simp [hji, G.adj_comm]
  rw [hbias] at hflip
  -- Reorient the flip-difference identity to match the Gibbs-fiber ordering.
  linarith

omit [DecidableEq Λ] in
/-- Helper for Example 18.18: the single-site Gibbs transition weight for the Ising Boltzmann law
is the explicit logistic conditional probability. -/
private lemma isingCoordinateTransitionWeight_eq_conditional
    (x y : ising_configuration Λ) (i : Λ) :
    gibbsCoordinateTransitionWeight (isingBoltzmannPMF G β) x i y =
      if y = gibbsCoordinateReplace x i (y i) then
        ENNReal.ofReal (isingConditionalProbability β G x i (y i))
      else
        0 := by
  classical
  rw [gibbsCoordinateTransitionWeight]
  by_cases hy : y = gibbsCoordinateReplace x i (y i)
  · rw [if_pos hy, if_pos hy]
    let σ : ising_spin := y i
    have hyσ : y = gibbsCoordinateReplace x i σ := by
      simpa [σ] using hy
    have hcore :
        isingBoltzmannPMF G β (gibbsCoordinateReplace x i σ) /
            gibbsCoordinateMarginal (isingBoltzmannPMF G β) x i =
          ENNReal.ofReal (isingConditionalProbability β G x i σ) := by
      have hmarg :
          gibbsCoordinateMarginal (isingBoltzmannPMF G β) x i =
            isingBoltzmannPMF G β (gibbsCoordinateReplace x i σ) +
              isingBoltzmannPMF G β (gibbsCoordinateReplace x i (flip_spin σ)) := by
        -- The one-site Ising fiber contains exactly the two spins `σ` and `flip_spin σ`.
        rw [gibbsCoordinateMarginal, tsum_fintype]
        simpa [σ] using
          (sum_isingSpin_eq_self_add_flip
            (f := fun τ : ising_spin ↦
              isingBoltzmannPMF G β (gibbsCoordinateReplace x i τ)) σ)
      let Z : ℝ≥0∞ := ∑' z : ising_configuration Λ, ising_boltzmann_weight G β z
      let a : ℝ := Real.exp (-β * hamiltonian G (gibbsCoordinateReplace x i σ))
      let b : ℝ := Real.exp (-β * hamiltonian G (gibbsCoordinateReplace x i (flip_spin σ)))
      have ha_pos : 0 < a := by
        exact Real.exp_pos _
      have hb_pos : 0 < b := by
        exact Real.exp_pos _
      have hZ_ne_top : Z ≠ ∞ := by
        simpa [Z] using isingBoltzmannPMF_tsum_ne_top (G := G) β
      have hZ_ne_zero : Z ≠ 0 := by
        simpa [Z] using isingBoltzmannPMF_tsum_ne_zero (G := G) β
      have hZinv_ne_zero : Z⁻¹ ≠ 0 := by
        exact ENNReal.inv_ne_zero.mpr hZ_ne_top
      have hZinv_ne_top : Z⁻¹ ≠ ∞ := by
        exact ENNReal.inv_ne_top.mpr hZ_ne_zero
      have hmass :
          isingBoltzmannPMF G β (gibbsCoordinateReplace x i σ) = ENNReal.ofReal a * Z⁻¹ := by
        simp [isingBoltzmannPMF, PMF.normalize_apply, ising_boltzmann_weight, Z, a]
      have hmassFlip :
          isingBoltzmannPMF G β (gibbsCoordinateReplace x i (flip_spin σ)) =
            ENNReal.ofReal b * Z⁻¹ := by
        simp [isingBoltzmannPMF, PMF.normalize_apply, ising_boltzmann_weight, Z, b]
      rw [hmarg, hmass, hmassFlip, ← add_mul]
      rw [ENNReal.mul_div_mul_right _ _ hZinv_ne_zero hZinv_ne_top]
      have hden_pos : 0 < a + b := add_pos ha_pos hb_pos
      rw [← ENNReal.ofReal_add ha_pos.le hb_pos.le, ← ENNReal.ofReal_div_of_pos hden_pos]
      have hratio :
          a / (a + b) = isingConditionalProbability β G x i σ := by
        let e : ℝ :=
          Real.exp
            (β *
              (hamiltonian G (gibbsCoordinateReplace x i σ) -
                hamiltonian G (gibbsCoordinateReplace x i (flip_spin σ))))
        have hratioExp : b / a = e := by
          -- The ratio of the two Boltzmann weights is determined by the energy difference.
          dsimp [a, b, e]
          rw [← Real.exp_sub]
          congr 1
          ring
        have hb_eq : b = a * e := by
          calc
            b = e * a := (div_eq_iff ha_pos.ne').mp hratioExp
            _ = a * e := by ring
        have hsum : a + b = a * (1 + e) := by
          rw [hb_eq]
          ring
        have hdiff :
            β *
                (hamiltonian G (gibbsCoordinateReplace x i σ) -
                  hamiltonian G (gibbsCoordinateReplace x i (flip_spin σ))) =
              2 * β * isingNeighborBias G x i σ := by
          rw [hamiltonian_replace_difference_eq_neighborBias (G := G) (x := x) (i := i) (σ := σ)]
          ring
        -- Rewrite the Boltzmann ratio into the logistic expression from the textbook.
        calc
          a / (a + b) = a / (a * (1 + e)) := by rw [hsum]
          _ = (1 + e)⁻¹ := by
            calc
              a / (a * (1 + e)) = (a * 1) / (a * (1 + e)) := by ring
              _ = 1 / (1 + e) := by rw [mul_div_mul_left _ _ ha_pos.ne']
              _ = (1 + e)⁻¹ := by simp [one_div]
          _ = (1 + Real.exp (2 * β * isingNeighborBias G x i σ))⁻¹ := by
            have heq : e = Real.exp (2 * β * isingNeighborBias G x i σ) := by
              simp [e, hdiff]
            rw [heq]
          _ = isingConditionalProbability β G x i σ := by
            rw [isingConditionalProbability]
      exact congrArg ENNReal.ofReal hratio
    rw [← hyσ] at hcore
    simpa [σ] using hcore
  · rw [if_neg hy, if_neg hy]

/- Example 18.18: the finite Ising Gibbs sampler is the Chapter 18 Gibbs sampler specialized to
the Ising Boltzmann distribution and the uniform site law on `Λ`. -/
#check (gibbsSamplerMatrix
  (PMF.uniformOfFintype Λ)
  (isingBoltzmannPMF G β) :
  ising_configuration Λ → ising_configuration Λ → ℝ≥0∞)

-- Proof sketch: rewrite with `gibbsSamplerMatrix_apply`, use that `PMF.uniformOfFintype Λ` gives
-- mass `(card Λ)⁻¹` to each site, and simplify the resulting single-site Gibbs ratio to the
-- logistic conditional law using positivity of the Ising Boltzmann weights.
/-- Evaluating the Ising specialization of `gibbsSamplerMatrix` reproduces the site-averaged
single-site conditional-probability formula. -/
theorem isingGibbsTransitionMatrix_apply
    (β : ℝ) (G : SimpleGraph Λ) [DecidableRel G.Adj]
    (x y : ising_configuration Λ) :
    gibbsSamplerMatrix
        (PMF.uniformOfFintype Λ)
        (isingBoltzmannPMF G β)
        x y =
      (Fintype.card Λ : ℝ≥0∞)⁻¹ *
        ∑ i : Λ,
          if y = gibbsCoordinateReplace x i (y i) then
            ENNReal.ofReal (isingConditionalProbability β G x i (y i))
          else
            0 := by
  -- Reduce the Gibbs-sampler matrix to its pointwise single-site transition weights.
  rw [gibbsSamplerMatrix_apply, tsum_fintype]
  simp_rw [PMF.uniformOfFintype_apply, isingCoordinateTransitionWeight_eq_conditional]
  -- The uniform site mass factors out of the finite sum.
  rw [← Finset.mul_sum]

end GibbsSampler

end ProbabilityTheory

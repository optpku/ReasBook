/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap18.Definition_18_14

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators ENNReal

noncomputable section

universe u

namespace ProbabilityTheory

variable {Λ : Type u} [Fintype Λ] [DecidableEq Λ]

/-- An Ising spin is a sign that is constrained to take only the values `-1` and `1`. -/
abbrev ising_spin : Type :=
  { s : SignType // s ≠ 0 }

/-- An Ising configuration assigns a spin to every site of the finite lattice `Λ`. -/
abbrev ising_configuration (Λ : Type u) : Type u :=
  Λ → ising_spin

-- Proof sketch: `σ.1` is a nonzero sign, and negation on `SignType` preserves nonzeroness on the
-- two-point subset `{ -1, 1 }`.
private theorem ising_spin_neg_ne_zero (σ : ising_spin) : (-σ.1 : SignType) ≠ 0 := by
  -- Negation preserves the nonzeroness that defines the Ising-spin subtype.
  simpa using σ.2

/-- Reversing an Ising spin exchanges `1` and `-1`. -/
def flip_spin (σ : ising_spin) : ising_spin :=
  ⟨-σ.1, ising_spin_neg_ne_zero σ⟩

/-- The configuration obtained from `x` by reversing the spin at the site `i`. -/
def flip_at (x : ising_configuration Λ) (i : Λ) : ising_configuration Λ :=
  Function.update x i (flip_spin (x i))

variable (G : SimpleGraph Λ) [DecidableRel G.Adj]

/-- The local Ising energy at the site `i` is half the number of neighboring spins that disagree
with the spin at `i`. -/
def local_energy (x : ising_configuration Λ) (i : Λ) : ℝ :=
  ∑ j, if G.Adj i j ∧ x i ≠ x j then (1 / 2 : ℝ) else 0

/-- The Hamiltonian of a finite Ising configuration is the sum of all local energies. -/
def hamiltonian (x : ising_configuration Λ) : ℝ :=
  ∑ i, local_energy G x i

/-- The unnormalized Boltzmann weight of the Ising configuration `x` at inverse temperature `β`. -/
def ising_boltzmann_weight (β : ℝ) (x : ising_configuration Λ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-β * hamiltonian G x))

variable [Nonempty Λ]

/-- The single-spin-flip proposal matrix chooses a site uniformly and proposes the configuration
obtained by reversing the spin at that site. -/
def ising_proposal_matrix (x y : ising_configuration Λ) : ℝ≥0∞ :=
  ∑ i, if y = flip_at x i then (Fintype.card Λ : ℝ≥0∞)⁻¹ else 0

section Metropolis

variable (β : ℝ)

/- Example 18.16: the finite Ising-model Metropolis matrix is the specialization of the general
Metropolis matrix to the single-spin-flip proposal and the Boltzmann weight
`x ↦ exp (-β H(x))`. -/
#check (metropolisMatrix (ising_boltzmann_weight G β) ising_proposal_matrix :
  ising_configuration Λ → ising_configuration Λ → ℝ≥0∞)

end Metropolis

/-- Helper for Example 18.16: every Ising spin is either `1` or `-1`. -/
private lemma ising_spin_eq_one_or_eq_neg_one (σ : ising_spin) : σ.1 = 1 ∨ σ.1 = -1 := by
  -- The excluded middle branch `σ.1 = 0` is ruled out by the subtype condition.
  rcases SignType.trichotomy σ.1 with hneg | hzero | hpos
  · exact Or.inr hneg
  · exact False.elim (σ.2 hzero)
  · exact Or.inl hpos

/-- Helper for Example 18.16: on the two-point Ising-spin space, being different from the flipped
spin is the same as being equal to the original spin. -/
private lemma ne_flipSpin_iff_eq {σ τ : ising_spin} : τ ≠ flip_spin σ ↔ τ = σ := by
  -- Reduce both spins to the concrete values `1` and `-1`, then simplify the subtype equality.
  rcases ising_spin_eq_one_or_eq_neg_one σ with hσ | hσ <;>
    rcases ising_spin_eq_one_or_eq_neg_one τ with hτ | hτ <;>
    simp [flip_spin, hσ, hτ, Subtype.ext_iff]

/-- Helper for Example 18.16: flipping an Ising spin never fixes it. -/
private lemma flipSpin_ne_self (σ : ising_spin) : flip_spin σ ≠ σ := by
  -- The two Ising spins are `1` and `-1`, so negation swaps them.
  rcases ising_spin_eq_one_or_eq_neg_one σ with hσ | hσ <;>
    simp [flip_spin, hσ, Subtype.ext_iff]

variable [Nonempty Λ]

/-- Helper for Example 18.16: the flipped site's local energy contributes one full copy of the
neighbor-bias sum appearing in the Hamiltonian difference formula. -/
private lemma localEnergy_flipAt_self_eq
    (x : ising_configuration Λ) (i : Λ) :
    local_energy G (flip_at x i) i - local_energy G x i =
      -∑ j, if G.Adj j i then (if x j ≠ x i then (1 : ℝ) else 0) - (1 / 2 : ℝ) else 0 := by
  -- Route correction: normalize the difference of finite sums into one sum of pointwise changes.
  -- Rewrite the difference as a sum of pointwise changes and simplify each neighbor term.
  rw [local_energy, local_energy, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  by_cases hadj : G.Adj j i
  · have hadji : G.Adj i j := (G.adj_comm j i).mp hadj
    have hji : j ≠ i := G.ne_of_adj hadj
    by_cases hneq : x j ≠ x i
    · have hflip : ¬ flip_spin (x i) ≠ x j := by
        intro hflipNe
        exact hneq <|
          (ne_flipSpin_iff_eq (σ := x i) (τ := x j)).mp (by simpa [ne_comm] using hflipNe)
      -- For a disagreeing neighbor, the flip removes the disagreement at `i`.
      have hneq' : x i ≠ x j := by simpa [ne_comm] using hneq
      simp [flip_at, hadj, hadji, hji, hneq, hneq', hflip]
      norm_num
    · have hflip : flip_spin (x i) ≠ x j := by
        have hxij : x i = x j := (by simpa [not_ne_iff] using hneq : x j = x i).symm
        simpa [hxij] using (flipSpin_ne_self (x j))
      -- For an agreeing neighbor, the flip creates the disagreement at `i`.
      have hxij : x i = x j := (by simpa [not_ne_iff] using hneq : x j = x i).symm
      simp [flip_at, hadj, hadji, hji, hxij, flipSpin_ne_self]
  · have hadji : ¬ G.Adj i j := by
      simpa [G.adj_comm i j] using hadj
    -- Non-neighbors contribute nothing before or after the flip.
    simp [hadj, hadji]

/-- Helper for Example 18.16: away from the flipped site, only the edge touching the flipped site
can change the local energy. -/
private lemma localEnergy_flipAt_of_ne_eq
    (x : ising_configuration Λ) (i k : Λ) (hki : k ≠ i) :
    local_energy G (flip_at x i) k - local_energy G x k =
      if G.Adj k i then -((if x k ≠ x i then (1 : ℝ) else 0) - (1 / 2 : ℝ)) else 0 := by
  -- Route correction: first rewrite the difference of local-energy sums as one finite sum.
  -- First isolate the unique summand `j = i`; all other neighbors of `k` are unchanged.
  rw [local_energy, local_energy, ← Finset.sum_sub_distrib]
  have hsum :
      ∑ j,
          ((if G.Adj k j ∧ (flip_at x i) k ≠ (flip_at x i) j then (1 / 2 : ℝ) else 0) -
            (if G.Adj k j ∧ x k ≠ x j then (1 / 2 : ℝ) else 0)) =
        ((if G.Adj k i ∧ (flip_at x i) k ≠ (flip_at x i) i then (1 / 2 : ℝ) else 0) -
          (if G.Adj k i ∧ x k ≠ x i then (1 / 2 : ℝ) else 0)) := by
    refine Finset.sum_eq_single i ?_ ?_
    · intro j _ hji
      have hk : (flip_at x i) k = x k := by
        simp [flip_at, hki]
      have hj : (flip_at x i) j = x j := by
        simp [flip_at, hji]
      -- Away from `i`, both endpoint spins are unchanged, so the summand cancels.
      simp [hk, hj]
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  rw [hsum]
  by_cases hneq : x k ≠ x i
  · have hflip : ¬ x k ≠ flip_spin (x i) := by
      intro hkflip
      exact hneq ((ne_flipSpin_iff_eq (σ := x i) (τ := x k)).mp hkflip)
    -- If `k` disagrees with `i`, then the flip destroys the only affected disagreement.
    simp [flip_at, hki, hneq, hflip]
    by_cases hAdj : G.Adj k i
    · simp [hAdj]
      norm_num
    · simp [hAdj]
  · have hflip : x k ≠ flip_spin (x i) := by
      have hxik : x i = x k := (by simpa [not_ne_iff] using hneq : x k = x i).symm
      simpa [hxik, ne_comm] using (flipSpin_ne_self (x k))
    -- If `k` agrees with `i`, then the flip creates the only affected disagreement.
    have hxik : x i = x k := (by simpa [not_ne_iff] using hneq : x k = x i).symm
    have hflipSelf : x k ≠ flip_spin (x k) := by
      simpa [ne_comm] using (flipSpin_ne_self (x k))
    simp [flip_at, hki, hxik, hflipSelf]

-- Proof sketch: only the energy contributions involving the flipped site and its neighbors change;
-- expanding those local terms yields the stated signed sum over neighboring disagreements.
/-- Flipping the spin at a site changes the Hamiltonian by the signed sum over its neighboring
disagreements. -/
theorem hamiltonian_flip_difference_eq
    (x : ising_configuration Λ) (i : Λ) :
    hamiltonian G (flip_at x i) - hamiltonian G x =
      -2 *
        ∑ j, if G.Adj j i then (if x j ≠ x i then (1 : ℝ) else 0) - (1 / 2 : ℝ) else 0 := by
  let Δ : Λ → ℝ :=
    fun j ↦ if G.Adj j i then (if x j ≠ x i then (1 : ℝ) else 0) - (1 / 2 : ℝ) else 0
  -- Expand the Hamiltonian difference into local-energy differences and split off the site `i`.
  rw [hamiltonian, hamiltonian, ← Finset.sum_sub_distrib]
  have hsplit :=
    Finset.sum_erase_add Finset.univ
      (fun k ↦ local_energy G (flip_at x i) k - local_energy G x k) (Finset.mem_univ i)
  rw [add_comm] at hsplit
  rw [← hsplit]
  have hothers :
      Finset.sum (Finset.univ.erase i)
          (fun k ↦ local_energy G (flip_at x i) k - local_energy G x k) =
        Finset.sum (Finset.univ.erase i) (fun k ↦ -(Δ k)) := by
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    have hki : k ≠ i := (Finset.mem_erase.mp hk).1
    -- Off the flipped site, the local-energy change is exactly the negated bias contribution.
    rw [localEnergy_flipAt_of_ne_eq (G := G) x i k hki]
    by_cases hAdj : G.Adj k i <;> by_cases hEq : x k = x i <;> simp [Δ, hAdj, hEq]
  have hdiag : Δ i = 0 := by
    -- The loopless condition removes the diagonal term from the bias sum.
    simp [Δ]
  have hothers_univ :
      Finset.sum (Finset.univ.erase i) (fun k ↦ -(Δ k)) =
        Finset.sum Finset.univ (fun k ↦ -(Δ k)) := by
    have hsplitΔ :=
      Finset.sum_erase_add Finset.univ (fun k ↦ -(Δ k)) (Finset.mem_univ i)
    rw [add_comm] at hsplitΔ
    simpa [hdiag] using hsplitΔ
  -- The site `i` contributes `-∑ Δ`, and every other site contributes the remaining `-Δ` term.
  calc
    (local_energy G (flip_at x i) i - local_energy G x i) +
        Finset.sum (Finset.univ.erase i)
          (fun k ↦ local_energy G (flip_at x i) k - local_energy G x k)
      =
        (-(∑ j, Δ j)) + Finset.sum (Finset.univ.erase i) (fun k ↦ -(Δ k)) := by
          rw [localEnergy_flipAt_self_eq (G := G) x i, hothers]
    _ = (-(∑ j, Δ j)) + Finset.sum Finset.univ (fun k ↦ -(Δ k)) := by rw [hothers_univ]
    _ = (-(∑ j, Δ j)) + -(∑ k, Δ k) := by rw [Finset.sum_neg_distrib]
    _ = -2 * ∑ j, Δ j := by ring
    _ =
        -2 *
          ∑ j, if G.Adj j i then (if x j ≠ x i then (1 : ℝ) else 0) - (1 / 2 : ℝ) else 0 := by
          simp [Δ]

end ProbabilityTheory

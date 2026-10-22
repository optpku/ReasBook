/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators InnerProduct

noncomputable section
open WithLp (toLp)

universe u

section

variable {ι : Type u} [Fintype ι]
variable {E : Type u}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "Eι" => PiLp (2 : ENNReal) (fun _ : ι ↦ E)

/- Example 6.16 is `source-facing`, expressed through the chapter's `core/canonical` owner
`prox[...]` on the canonical `PiLp (2 : ENNReal)` finite product. Domain sampling against
Definition 6.1, Theorem 6.6, Theorem 6.11, and Theorem 6.15 shows that the correct ambient
abstraction is an arbitrary finite index type `ι`: the mathematics uses only the finite family sum
and its cardinality, while the equal-coordinate `Fin m` presentation is merely a concrete view.
The primitive data are therefore `g`, its canonical properness witness
`IsProperExtendedRealFunction g`, `x`, and the finite index set; the coordinate-sum map and
constant-tuple correction are derived bridge data rather than a second public owner. The review
counterexample `g ≡ ⊤` shows that the nonempty-effective-domain half of properness is
semantically active here, so the source-facing example should reuse the project owner
`IsProperExtendedRealFunction` instead of a local no-`⊥` fragment. Theorem 6.15 is still the
right `bridge/view` owner for the Hilbert-space transport pattern, but its `CompleteSpace`-based
adjoint interface is stronger than the present source-facing example, so only the properness owner
is imported here rather than the full affine-map bridge. -/

-- Proof sketch: if `ι` is empty, then `PiLp (2 : ENNReal) (fun _ : ι ↦ E)` is a singleton, and
-- both sides reduce to that singleton. Otherwise write the proximal objective for
-- `y ↦ g (∑ i, y i)` on the canonical product model `PiLp (2 : ENNReal)`. The summation map has
-- adjoint the constant-tuple map `z ↦ (z, …, z)`, so the quadratic correction is a common
-- coordinate shift by `(1 / Fintype.card ι) • (z - ∑ i, x i)`. The hypothesis
-- `IsProperExtendedRealFunction g` supplies both the no-`⊥` condition and a finite-value witness,
-- preventing the degenerate `g ≡ ⊤` case in which the pulled-back proximal objective is constant
-- `⊤` on every affine fiber. This identifies the minimizing sets with the proximal set of
-- `(Fintype.card ι) g` at `∑ i, x i`.
/-- Helper for Example 6.16: constant tuples implement the adjoint of the coordinate-sum map. -/
lemma constant_tuple_inner_eq_sum_inner (x : Eι) (z : E) :
    inner ℝ (toLp 2 (fun _ : ι ↦ z)) x = inner ℝ z (∑ i, x i) := by
  -- Rewrite the `PiLp` inner product as a finite sum and collapse the repeated coordinate.
  rw [PiLp.inner_apply]
  simpa using (inner_sum (s := Finset.univ) (f := fun i : ι ↦ x i) (x := z)).symm

/-- Helper for Example 6.16: the squared norm of a constant tuple scales by the cardinality. -/
lemma constant_tuple_norm_sq (z : E) :
    ‖(toLp 2 (fun _ : ι ↦ z) : Eι)‖ ^ (2 : ℕ) = (Fintype.card ι : ℝ) * ‖z‖ ^ (2 : ℕ) := by
  -- The canonical `PiLp` `L²` formula turns the norm square into a repeated finite sum.
  rw [PiLp.norm_sq_eq_of_L2]
  simp

/-- Helper for Example 6.16: the average-shift section has coordinate sum equal to the target
value `z`. -/
lemma sum_average_shift_eq (hcard : 0 < Fintype.card ι) (x : Eι) (z : E) :
    (∑ i,
      (x + toLp 2 (fun _ : ι ↦ (1 / (Fintype.card ι : ℝ)) • (z - ∑ j, x j)) : Eι) i) = z := by
  -- Summing the translated constant tuple recovers the prescribed codomain point.
  simp [Finset.sum_add_distrib, hcard.ne', smul_smul, add_assoc, add_comm, sub_eq_add_neg,
    ← Nat.cast_smul_eq_nsmul ℝ]

/-- Helper for Example 6.16: each fiber splits into the constant average correction and a
zero-sum residual, and the split is orthogonal. -/
lemma average_shift_norm_sq_split (hcard : 0 < Fintype.card ι) (x u : Eι) :
    let δ : E := (1 / (Fintype.card ι : ℝ)) • ((∑ i, u i) - (∑ i, x i))
    ‖u - x‖ ^ (2 : ℕ) =
      ‖toLp 2 (fun _ : ι ↦ δ)‖ ^ (2 : ℕ) +
        ‖u - x - toLp 2 (fun _ : ι ↦ δ)‖ ^ (2 : ℕ) := by
  let δ : E := (1 / (Fintype.card ι : ℝ)) • ((∑ i, u i) - (∑ i, x i))
  let c : Eι := toLp 2 (fun _ : ι ↦ δ)
  let r : Eι := u - x - c
  have hsum_zero : ∑ i, (r : Eι) i = 0 := by
    -- The residual lies in the kernel of the coordinate-sum map.
    calc
      ∑ i, (r : Eι) i = (∑ i, (u - x : Eι) i) - ∑ i, (c : Eι) i := by
            simp [r]
      _ = ((∑ i, u i) - (∑ i, x i)) - (Fintype.card ι : ℕ) • δ := by
            simp [c]
      _ = ((∑ i, u i) - (∑ i, x i)) - (Fintype.card ι : ℝ) • δ := by
            rw [← Nat.cast_smul_eq_nsmul ℝ]
      _ = 0 := by
            simp [δ, smul_smul, hcard.ne']
  have horth : inner ℝ c r = 0 := by
    -- Orthogonality comes from pairing a constant tuple with a zero-sum residual.
    dsimp [c]
    rw [constant_tuple_inner_eq_sum_inner, hsum_zero]
    simp
  have hdecomp : u - x = c + r := by
    -- This is the defining decomposition of the affine fiber.
    ext i
    simp [c, r, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  -- Apply the real Pythagorean identity to the orthogonal decomposition.
  calc
    ‖u - x‖ ^ (2 : ℕ) = ‖c + r‖ ^ (2 : ℕ) := by
          rw [hdecomp]
    _ = ‖c‖ ^ (2 : ℕ) + 2 * inner ℝ c r + ‖r‖ ^ (2 : ℕ) := norm_add_sq_real _ _
    _ = ‖c‖ ^ (2 : ℕ) + ‖r‖ ^ (2 : ℕ) := by
          simp [horth]
    _ = ‖toLp 2 (fun _ : ι ↦ δ)‖ ^ (2 : ℕ) + ‖u - x - toLp 2 (fun _ : ι ↦ δ)‖ ^ (2 : ℕ) := by
          simp [c, r]

/-- Helper for Example 6.16: on the canonical average-shift section, the scaled codomain
objective equals the pullback objective multiplied by the cardinality. -/
lemma scaled_objective_on_average_shift
    (g : E → EReal) (hcard : 0 < Fintype.card ι) (x : Eι) (z : E) :
    proximal_objective (((Fintype.card ι : ℝ) : EReal) • g) (∑ i, x i) z =
      (((Fintype.card ι : ℝ) : EReal) *
        proximal_objective (fun y : Eι ↦ g (∑ i, y i)) x
          (x + toLp 2 (fun _ : ι ↦ (1 / (Fintype.card ι : ℝ)) • (z - ∑ i, x i)))) := by
  let s : EReal := ((Fintype.card ι : ℝ) : EReal)
  have hs_nonneg_real : 0 ≤ (Fintype.card ι : ℝ) := by
    positivity
  have hs_nonneg : 0 ≤ s := by
    change (0 : EReal) ≤ ((Fintype.card ι : ℝ) : EReal)
    exact_mod_cast hs_nonneg_real
  have hs_top : s ≠ ⊤ := EReal.coe_ne_top _
  have hinv_nonneg : 0 ≤ (1 / (Fintype.card ι : ℝ)) := by
    positivity
  have hquad_real :
      ((1 / 2 : ℝ) * ‖z - ∑ i, x i‖ ^ (2 : ℕ)) =
        (Fintype.card ι : ℝ) *
          ((1 / 2 : ℝ) *
            ‖(toLp 2 (fun _ : ι ↦ (1 / (Fintype.card ι : ℝ)) • (z - ∑ i, x i)) : Eι)‖ ^
              (2 : ℕ)) := by
    -- The constant-tuple norm formula supplies the exact cardinality scaling.
    rw [constant_tuple_norm_sq]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hinv_nonneg]
    field_simp [hcard.ne']
  have hquad :
      ((((1 / 2 : ℝ) * ‖z - ∑ i, x i‖ ^ (2 : ℕ)) : ℝ) : EReal) =
        (((Fintype.card ι : ℝ) : EReal) *
          (((((1 / 2 : ℝ) *
            ‖(toLp 2 (fun _ : ι ↦ (1 / (Fintype.card ι : ℝ)) • (z - ∑ i, x i)) : Eι)‖ ^
              (2 : ℕ)) : ℝ)) : EReal)) := by
    exact_mod_cast hquad_real
  have hsection :
      g z +
          (((((1 / 2 : ℝ) *
            ‖(toLp 2 (fun _ : ι ↦ (1 / (Fintype.card ι : ℝ)) • (z - ∑ i, x i)) : Eι)‖ ^
              (2 : ℕ)) : ℝ)) : EReal) =
        proximal_objective (fun y : Eι ↦ g (∑ i, y i)) x
          (x + toLp 2 (fun _ : ι ↦ (1 / (Fintype.card ι : ℝ)) • (z - ∑ i, x i))) := by
    -- Evaluating the pullback objective on the section replaces the sum by `z`.
    rw [proximal_objective_apply, sum_average_shift_eq hcard x z]
    simp
  calc
    proximal_objective (((Fintype.card ι : ℝ) : EReal) • g) (∑ i, x i) z
        = s * g z + ((((1 / 2 : ℝ) * ‖z - ∑ i, x i‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
            simp [proximal_objective, s]
    _ = s * g z +
          (s * (((((1 / 2 : ℝ) *
            ‖(toLp 2 (fun _ : ι ↦ (1 / (Fintype.card ι : ℝ)) • (z - ∑ i, x i)) : Eι)‖ ^
              (2 : ℕ)) : ℝ)) : EReal)) := by
            rw [hquad]
    _ = s *
          (g z +
            (((((1 / 2 : ℝ) *
              ‖(toLp 2 (fun _ : ι ↦ (1 / (Fintype.card ι : ℝ)) • (z - ∑ i, x i)) : Eι)‖ ^
                (2 : ℕ)) : ℝ)) : EReal)) := by
            rw [EReal.left_distrib_of_nonneg_of_ne_top hs_nonneg hs_top]
    _ = s * proximal_objective (fun y : Eι ↦ g (∑ i, y i)) x
          (x + toLp 2 (fun _ : ι ↦ (1 / (Fintype.card ι : ℝ)) • (z - ∑ i, x i))) := by
            simpa [s] using congrArg (fun t : EReal ↦ s * t) hsection

/-- Helper for Example 6.16: along an arbitrary fiber, the scaled codomain objective is bounded
above by the pullback objective. -/
lemma scaled_objective_le_along_sum_fiber
    (g : E → EReal) (hcard : 0 < Fintype.card ι) (x u : Eι) :
    proximal_objective (((Fintype.card ι : ℝ) : EReal) • g) (∑ i, x i) (∑ i, u i) ≤
      (((Fintype.card ι : ℝ) : EReal) *
        proximal_objective (fun y : Eι ↦ g (∑ i, y i)) x u) := by
  let s : EReal := ((Fintype.card ι : ℝ) : EReal)
  let δ : E := (1 / (Fintype.card ι : ℝ)) • ((∑ i, u i) - (∑ i, x i))
  have hs_nonneg_real : 0 ≤ (Fintype.card ι : ℝ) := by
    positivity
  have hs_nonneg : 0 ≤ s := by
    change (0 : EReal) ≤ ((Fintype.card ι : ℝ) : EReal)
    exact_mod_cast hs_nonneg_real
  have hs_top : s ≠ ⊤ := EReal.coe_ne_top _
  have hinv_nonneg : 0 ≤ (1 / (Fintype.card ι : ℝ)) := by
    positivity
  have hsplit := average_shift_norm_sq_split (ι := ι) (E := E) hcard x u
  have hconst : ‖(toLp 2 (fun _ : ι ↦ δ) : Eι)‖ ^ (2 : ℕ) =
      (1 / (Fintype.card ι : ℝ)) * ‖(∑ i, u i) - (∑ i, x i)‖ ^ (2 : ℕ) := by
    -- Rewrite the constant-tuple norm in the averaged coordinates.
    rw [constant_tuple_norm_sq]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hinv_nonneg]
    field_simp [hcard.ne']
  have hres_nonneg : 0 ≤ ‖u - x - toLp 2 (fun _ : ι ↦ δ)‖ ^ (2 : ℕ) := by
    positivity
  have hbase :
      (1 / (Fintype.card ι : ℝ)) * ‖(∑ i, u i) - (∑ i, x i)‖ ^ (2 : ℕ) ≤ ‖u - x‖ ^ (2 : ℕ) := by
    -- The residual square is nonnegative, so dropping it only lowers the norm split.
    rw [hsplit, hconst]
    nlinarith
  have hsq_le : ‖(∑ i, u i) - (∑ i, x i)‖ ^ (2 : ℕ) ≤ (Fintype.card ι : ℝ) * ‖u - x‖ ^ (2 : ℕ) := by
    have hcardR_pos : 0 < (Fintype.card ι : ℝ) := by
      positivity
    calc
      ‖(∑ i, u i) - (∑ i, x i)‖ ^ (2 : ℕ)
          = (Fintype.card ι : ℝ) *
              ((1 / (Fintype.card ι : ℝ)) * ‖(∑ i, u i) - (∑ i, x i)‖ ^ (2 : ℕ)) := by
                field_simp [hcard.ne']
      _ ≤ (Fintype.card ι : ℝ) * ‖u - x‖ ^ (2 : ℕ) :=
            mul_le_mul_of_nonneg_left hbase hcardR_pos.le
  have hhalf :
      ((1 / 2 : ℝ) * ‖(∑ i, u i) - (∑ i, x i)‖ ^ (2 : ℕ)) ≤
        (Fintype.card ι : ℝ) * ((1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ)) := by
    -- Multiply the squared-norm comparison by the common nonnegative factor `1 / 2`.
    have hhalf_base := mul_le_mul_of_nonneg_left hsq_le (show 0 ≤ (1 / 2 : ℝ) by positivity)
    simpa [mul_assoc, mul_left_comm, mul_comm] using hhalf_base
  have hquad :
      ((((1 / 2 : ℝ) * ‖(∑ i, u i) - (∑ i, x i)‖ ^ (2 : ℕ)) : ℝ) : EReal) ≤
        (((Fintype.card ι : ℝ) : EReal) *
          (((((1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ)) : ℝ)) : EReal)) := by
    exact_mod_cast hhalf
  -- Compare the codomain quadratic term against the product-space quadratic term.
  calc
    proximal_objective (((Fintype.card ι : ℝ) : EReal) • g) (∑ i, x i) (∑ i, u i)
        = s * g (∑ i, u i) +
            ((((1 / 2 : ℝ) * ‖(∑ i, u i) - (∑ i, x i)‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
            simp [proximal_objective, s]
    _ ≤ s * g (∑ i, u i) +
          (s * (((((1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ)) : ℝ)) : EReal)) := by
            simpa [add_assoc, add_left_comm, add_comm] using
              add_le_add_left hquad (s * g (∑ i, u i))
    _ = s * (g (∑ i, u i) + (((((1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ)) : ℝ)) : EReal)) := by
            rw [EReal.left_distrib_of_nonneg_of_ne_top hs_nonneg hs_top]
    _ = s * proximal_objective (fun y : Eι ↦ g (∑ i, y i)) x u := by
            simp [proximal_objective, s]

/-- Helper for Example 6.16: the zero vector minimizes the proximal objective of the zero-scaled
function at the origin. -/
lemma zero_mem_prox_zero_smul (g : E → EReal) :
    (0 : E) ∈ prox[((0 : ℝ) : EReal) • g] 0 := by
  rw [mem_proximal_mapping_iff, isMinOn_univ_iff]
  intro z
  have hnonneg_real : 0 ≤ (1 / 2 : ℝ) * ‖z‖ ^ (2 : ℕ) := by
    positivity
  have hnonneg : (0 : EReal) ≤ ((((1 / 2 : ℝ) * ‖z‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
    exact_mod_cast hnonneg_real
  simpa [proximal_objective] using hnonneg

/-- Helper for Example 6.16: a pullback proximal minimizer maps to a proximal minimizer of the
scaled codomain objective. -/
private lemma pullback_minimizer_maps_to_scaled_minimizer
    (g : E → EReal) (hcard : 0 < Fintype.card ι) (x u : Eι)
    (hu : u ∈ prox[fun y : Eι ↦ g (∑ i, y i)] x) :
    (∑ i, u i) ∈ prox[((Fintype.card ι : ℝ) : EReal) • g] (∑ i, x i) := by
  let T : E → Eι := fun z ↦
    x + toLp 2 (fun _ : ι ↦ (1 / (Fintype.card ι : ℝ)) • (z - ∑ i, x i))
  have hs_nonneg_real : 0 ≤ (Fintype.card ι : ℝ) := by
    positivity
  have hs_nonneg : 0 ≤ (((Fintype.card ι : ℝ) : EReal)) := by
    exact_mod_cast hs_nonneg_real
  rw [mem_proximal_mapping_iff] at hu ⊢
  rw [isMinOn_univ_iff] at hu ⊢
  intro z
  have huz :
      proximal_objective (fun y : Eι ↦ g (∑ i, y i)) x u ≤
        proximal_objective (fun y : Eι ↦ g (∑ i, y i)) x (T z) := hu (T z)
  have hscaled :
      (((Fintype.card ι : ℝ) : EReal) * proximal_objective (fun y : Eι ↦ g (∑ i, y i)) x u) ≤
        (((Fintype.card ι : ℝ) : EReal) *
          proximal_objective (fun y : Eι ↦ g (∑ i, y i)) x (T z)) :=
    mul_le_mul_of_nonneg_left huz hs_nonneg
  -- Compare the pullback minimizer against the canonical section over `z`.
  calc
    proximal_objective (((Fintype.card ι : ℝ) : EReal) • g) (∑ i, x i) (∑ i, u i)
        ≤ (((Fintype.card ι : ℝ) : EReal) *
            proximal_objective (fun y : Eι ↦ g (∑ i, y i)) x u) :=
          scaled_objective_le_along_sum_fiber g hcard x u
    _ ≤ (((Fintype.card ι : ℝ) : EReal) *
          proximal_objective (fun y : Eι ↦ g (∑ i, y i)) x (T z)) := hscaled
    _ = proximal_objective (((Fintype.card ι : ℝ) : EReal) • g) (∑ i, x i) z := by
          simpa [T] using (scaled_objective_on_average_shift g hcard x z).symm

/-- Helper for Example 6.16: a pullback proximal minimizer must equal the canonical average-shift
section above its summed image. -/
lemma pullback_minimizer_eq_average_shift
    (g : E → EReal) (hg_proper : IsProperExtendedRealFunction g)
    (hcard : 0 < Fintype.card ι) (x u : Eι)
    (hu : u ∈ prox[fun y : Eι ↦ g (∑ i, y i)] x) :
    u = x + toLp 2 (fun _ : ι ↦ (1 / (Fintype.card ι : ℝ)) • ((∑ i, u i) - (∑ i, x i))) := by
  let T : E → Eι := fun z ↦
    x + toLp 2 (fun _ : ι ↦ (1 / (Fintype.card ι : ℝ)) • (z - ∑ i, x i))
  rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hu
  rcases hg_proper.effective_domain_nonempty with ⟨z₀, hz₀_eff⟩
  have hz₀_top : g z₀ ≠ ⊤ := (mem_effective_domain.mp hz₀_eff).ne
  have hobj_Tz₀_top : proximal_objective (fun y : Eι ↦ g (∑ i, y i)) x (T z₀) ≠ ⊤ := by
    -- Properness gives a finite competitor on the canonical section.
    intro htop
    have hfinite :
        g z₀ + ((((1 / 2 : ℝ) * ‖T z₀ - x‖ ^ (2 : ℕ)) : ℝ) : EReal) ≠ ⊤ :=
      EReal.add_ne_top hz₀_top (EReal.coe_ne_top _)
    have htop' := htop
    rw [proximal_objective_apply, sum_average_shift_eq hcard x z₀] at htop'
    exact hfinite htop'
  have hgu_top : g (∑ i, u i) ≠ ⊤ := by
    -- A minimizer cannot lie above a finite competitor.
    intro hgu_top
    have hcompare₀ :
        proximal_objective (fun y : Eι ↦ g (∑ i, y i)) x u ≤
          proximal_objective (fun y : Eι ↦ g (∑ i, y i)) x (T z₀) := hu (T z₀)
    have htop_eq : proximal_objective (fun y : Eι ↦ g (∑ i, y i)) x u = ⊤ := by
      calc
        proximal_objective (fun y : Eι ↦ g (∑ i, y i)) x u
            = g (∑ i, u i) + ((((1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
                simp [proximal_objective_apply]
        _ = ⊤ := by
              rw [hgu_top, EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)]
    have htop_le : (⊤ : EReal) ≤ proximal_objective (fun y : Eι ↦ g (∑ i, y i)) x (T z₀) := by
      calc
        (⊤ : EReal) = proximal_objective (fun y : Eι ↦ g (∑ i, y i)) x u := htop_eq.symm
        _ ≤ proximal_objective (fun y : Eι ↦ g (∑ i, y i)) x (T z₀) := hcompare₀
    exact hobj_Tz₀_top (top_le_iff.mp htop_le)
  let Tu : Eι := T (∑ i, u i)
  have hsumTu : (∑ i, Tu i) = ∑ i, u i := by
    simpa [Tu, T] using sum_average_shift_eq hcard x (∑ i, u i)
  have hcompare :
      proximal_objective (fun y : Eι ↦ g (∑ i, y i)) x u ≤
        proximal_objective (fun y : Eι ↦ g (∑ i, y i)) x Tu := hu Tu
  have hcompare_real :
      (g (∑ i, u i)).toReal + (1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ) ≤
        (g (∑ i, u i)).toReal + (1 / 2 : ℝ) * ‖Tu - x‖ ^ (2 : ℕ) := by
    -- After ruling out `⊤`, both proximal values can be compared in `ℝ`.
    have hg_sum_ne_bot : g (∑ i, u i) ≠ ⊥ := hg_proper.ne_bot _
    exact EReal.coe_le_coe_iff.mp <| by
      simpa [proximal_objective_apply, hsumTu, EReal.coe_add,
        EReal.coe_toReal hgu_top hg_sum_ne_bot] using hcompare
  have hsq_le : ‖u - x‖ ^ (2 : ℕ) ≤ ‖Tu - x‖ ^ (2 : ℕ) := by
    nlinarith
  have hTu_sub :
      Tu - x =
        toLp 2 (fun _ : ι ↦ (1 / (Fintype.card ι : ℝ)) • ((∑ i, u i) - (∑ i, x i))) := by
    simp [Tu, T]
  have huTu_sub : u - x - (Tu - x) = u - Tu := by
    -- The residual from the norm split is exactly the difference `u - Tu`.
    ext i
    simp [Tu, T, sub_eq_add_neg, add_assoc, add_comm]
  have hsplit : ‖u - x‖ ^ (2 : ℕ) = ‖Tu - x‖ ^ (2 : ℕ) + ‖u - Tu‖ ^ (2 : ℕ) := by
    -- Rewrite the abstract fiber split using the concrete section point `Tu`.
    calc
      ‖u - x‖ ^ (2 : ℕ)
          = ‖toLp 2 (fun _ : ι ↦ (1 / (Fintype.card ι : ℝ)) • ((∑ i, u i) - (∑ i, x i)))‖ ^
              (2 : ℕ) +
            ‖u - x -
                toLp 2 (fun _ : ι ↦ (1 / (Fintype.card ι : ℝ)) • ((∑ i, u i) - (∑ i, x i)))‖ ^
              (2 : ℕ) :=
            average_shift_norm_sq_split (ι := ι) (E := E) hcard x u
      _ = ‖Tu - x‖ ^ (2 : ℕ) + ‖u - Tu‖ ^ (2 : ℕ) := by
            rw [← hTu_sub, huTu_sub]
  have hres_zero : ‖u - Tu‖ ^ (2 : ℕ) = 0 := by
    nlinarith [hsplit, hsq_le]
  have hnorm_zero : ‖u - Tu‖ = 0 := eq_zero_of_pow_eq_zero hres_zero
  have hu_eq_Tu : u = Tu := sub_eq_zero.mp (norm_eq_zero.mp hnorm_zero)
  simpa [Tu, T] using hu_eq_Tu

/-- Example 6.16: on the canonical finite `L²` product `PiLp (2 : ENNReal)`, if
`f x = g (∑ i, x i)`, then the proximal set of `f` at `x` is obtained by choosing a proximal
point `z` of `(Fintype.card ι) g` at `∑ i, x i` and translating `x` by the constant tuple with
common value `(1 / Fintype.card ι) • (z - ∑ i, x i)`. The textbook `m`-tuple formula is the
specialization `ι = Fin m`; the empty family case is included and both sides are the unique point
of the empty product. The semantically active hypothesis is the canonical properness owner
`IsProperExtendedRealFunction g`, whose effective-domain witness rules out the degenerate
`g ≡ ⊤` case; stronger textbook closedness and convexity assumptions remain unnecessary. -/
theorem proximal_mapping_sum_precompose_eq_image
    (g : E → EReal) (hg_proper : IsProperExtendedRealFunction g) (x : Eι) :
    prox[fun y : Eι ↦ g (∑ i, y i)] x =
      (fun z : E ↦
        x + toLp 2 (fun _ : ι ↦ (1 / (Fintype.card ι : ℝ)) • (z - ∑ i, x i))) ''
        prox[((Fintype.card ι : ℝ) : EReal) • g] (∑ i, x i) := by
  by_cases hι : Nonempty ι
  · let T : E → Eι := fun z ↦
      x + toLp 2 (fun _ : ι ↦ (1 / (Fintype.card ι : ℝ)) • (z - ∑ i, x i))
    have hcard : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr hι
    have hs_nonneg_real : 0 ≤ (Fintype.card ι : ℝ) := by
      positivity
    have hs_nonneg : 0 ≤ (((Fintype.card ι : ℝ) : EReal)) := by
      exact_mod_cast hs_nonneg_real
    have hs_top : (((Fintype.card ι : ℝ) : EReal)) ≠ ⊤ := EReal.coe_ne_top _
    have hs_bot : (((Fintype.card ι : ℝ) : EReal)) ≠ ⊥ := EReal.coe_ne_bot _
    have hs_zero : (((Fintype.card ι : ℝ) : EReal)) ≠ 0 := by
      exact_mod_cast hcard.ne'
    ext u
    constructor
    · intro hu
      rw [Set.mem_image]
      refine ⟨∑ i, u i, pullback_minimizer_maps_to_scaled_minimizer g hcard x u hu, ?_⟩
      -- A pullback minimizer must lie on the canonical average-shift section.
      simpa [T] using (pullback_minimizer_eq_average_shift g hg_proper hcard x u hu).symm
    · rintro ⟨z, hz, rfl⟩
      rw [mem_proximal_mapping_iff] at hz ⊢
      rw [isMinOn_univ_iff] at hz ⊢
      intro v
      have hscaled :
          (((Fintype.card ι : ℝ) : EReal) *
            proximal_objective (fun y : Eι ↦ g (∑ i, y i)) x (T z)) ≤
            (((Fintype.card ι : ℝ) : EReal) *
              proximal_objective (fun y : Eι ↦ g (∑ i, y i)) x v) := by
        -- Route correction: scale once in `EReal`, compare on the codomain, then divide back.
        calc
          (((Fintype.card ι : ℝ) : EReal) *
              proximal_objective (fun y : Eι ↦ g (∑ i, y i)) x (T z)) =
              proximal_objective (((Fintype.card ι : ℝ) : EReal) • g) (∑ i, x i) z := by
                simpa [T] using (scaled_objective_on_average_shift g hcard x z).symm
          _ ≤ proximal_objective (((Fintype.card ι : ℝ) : EReal) • g) (∑ i, x i) (∑ i, v i) :=
                hz (∑ i, v i)
          _ ≤ (((Fintype.card ι : ℝ) : EReal) *
                proximal_objective (fun y : Eι ↦ g (∑ i, y i)) x v) :=
              scaled_objective_le_along_sum_fiber g hcard x v
      have hdiv :
          ((((Fintype.card ι : ℝ) : EReal) *
              proximal_objective (fun y : Eι ↦ g (∑ i, y i)) x (T z)) /
              ((Fintype.card ι : ℝ) : EReal)) ≤
            ((((Fintype.card ι : ℝ) : EReal) *
                proximal_objective (fun y : Eι ↦ g (∑ i, y i)) x v) /
                ((Fintype.card ι : ℝ) : EReal)) :=
        EReal.monotone_div_right_of_nonneg hs_nonneg hscaled
      rw [mul_comm (((Fintype.card ι : ℝ) : EReal))
            (proximal_objective (fun y : Eι ↦ g (∑ i, y i)) x (T z)),
        mul_comm (((Fintype.card ι : ℝ) : EReal))
            (proximal_objective (fun y : Eι ↦ g (∑ i, y i)) x v),
        ← EReal.mul_div_right,
        ← EReal.mul_div_right,
        EReal.div_mul_cancel hs_bot hs_top hs_zero,
        EReal.div_mul_cancel hs_bot hs_top hs_zero] at hdiv
      simpa [T] using hdiv
  · letI : IsEmpty ι := not_nonempty_iff.mp hι
    letI : Subsingleton Eι := inferInstance
    have hleft : prox[fun y : Eι ↦ g (∑ i, y i)] x = {x} := by
      have hprox_all : ∀ u : Eι, u ∈ prox[fun y : Eι ↦ g (∑ i, y i)] x := by
        intro u
        rw [mem_proximal_mapping_iff, isMinOn_univ_iff]
        intro v
        have huv : u = v := Subsingleton.elim u v
        simp [huv]
      ext u
      constructor
      · intro _
        simpa using (Subsingleton.elim u x)
      · intro _
        exact hprox_all u
    have hsumx : (∑ i, x i) = 0 := by
      simp
    have hcard_zero : (Fintype.card ι : ℝ) = 0 := by
      simp
    have h0mem : (0 : E) ∈ prox[((Fintype.card ι : ℝ) : EReal) • g] (∑ i, x i) := by
      rw [hsumx, hcard_zero]
      exact zero_mem_prox_zero_smul g
    have hright :
        (fun z : E ↦ x + toLp 2 (fun _ : ι ↦ (1 / (Fintype.card ι : ℝ)) • (z - ∑ i, x i))) ''
          prox[((Fintype.card ι : ℝ) : EReal) • g] (∑ i, x i) = {x} := by
      ext u
      constructor
      · rintro ⟨z, hz, rfl⟩
        rw [Set.mem_singleton_iff]
        have hzero :
            (toLp 2 (fun _ : ι ↦ (1 / (Fintype.card ι : ℝ)) • (z - ∑ i, x i)) : Eι) = 0 := by
          ext i
          exact False.elim (isEmptyElim i)
        change x + toLp 2 (fun _ : ι ↦ (1 / (Fintype.card ι : ℝ)) • (z - ∑ i, x i)) = x
        rw [hzero, add_zero]
      · intro hu
        rw [Set.mem_singleton_iff] at hu
        subst u
        refine ⟨0, h0mem, ?_⟩
        have hzero :
            (toLp 2 (fun _ : ι ↦ (1 / (Fintype.card ι : ℝ)) • (0 - ∑ i, x i)) : Eι) = 0 := by
          ext i
          exact False.elim (isEmptyElim i)
        change x + toLp 2 (fun _ : ι ↦ (1 / (Fintype.card ι : ℝ)) • (0 - ∑ i, x i)) = x
        rw [hzero, add_zero]
    rw [hleft, hright]

end

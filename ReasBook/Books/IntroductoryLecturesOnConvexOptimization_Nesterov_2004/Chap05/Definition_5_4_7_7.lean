/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

noncomputable section

variable (n : ℕ)

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "LpLiftPointₙ" => ℝ × Eₙ × Eₙ

/-- Helper for Definition 5.4.7.7: the scalar coordinate barrier appearing in each summand of
`Ψ_α`. -/
private def power_cone_barrier (α : ℝ) : ((ℝ × ℝ) × ℝ) → ℝ :=
  fun p ↦
    -Real.log
        (Real.rpow p.1.1 (2 * α) * Real.rpow p.1.2 (2 * (1 - α)) - p.2 ^ (2 : ℕ)) -
      Real.log p.1.1 - Real.log p.1.2

/-- Helper for Definition 5.4.7.7: the weighted geometric mean `x₁^α x₂^(1 - α)` appearing in
the scalar power-cone inequality. -/
private def powerConeGeometricMean (α : ℝ) (x : ℝ × ℝ) : ℝ :=
  Real.rpow x.1 α * Real.rpow x.2 (1 - α)

/-- Helper for Definition 5.4.7.7: evaluating `powerConeGeometricMean α` at `(x₁, x₂)` gives the
expected `Real.rpow` product. -/
private theorem powerConeGeometricMean_apply (α x₁ x₂ : ℝ) :
    powerConeGeometricMean α (x₁, x₂) =
      Real.rpow x₁ α * Real.rpow x₂ (1 - α) :=
  rfl

/-- Helper for Definition 5.4.7.7: the orthant `Q₁ = ℝ_+²` consists of pairs with both
coordinates nonnegative. -/
private def powerConeQ1 : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ 0 ≤ p.2}

/-- Helper for Definition 5.4.7.7: membership in `powerConeQ1` is the pair of nonnegativity
inequalities. -/
private theorem mem_powerConeQ1_iff (x₁ x₂ : ℝ) :
    (x₁, x₂) ∈ powerConeQ1 ↔ 0 ≤ x₁ ∧ 0 ≤ x₂ :=
  Iff.rfl

/-- Helper for Definition 5.4.7.7: the planar comparison set `Q₂` is the region `|z| ≤ y`. -/
private def powerConeQ2 : Set (ℝ × ℝ) :=
  {p | |p.2| ≤ p.1}

/-- Helper for Definition 5.4.7.7: membership in `powerConeQ2` is the scalar inequality
`|z| ≤ y`. -/
private theorem mem_powerConeQ2_iff (y z : ℝ) :
    (y, z) ∈ powerConeQ2 ↔ |z| ≤ y :=
  Iff.rfl

/-- Helper for Definition 5.4.7.7: the scalar power cone consists of nonnegative coordinates
together with the geometric-mean bound on `z`. -/
private def powerCone (α : ℝ) : Set ((ℝ × ℝ) × ℝ) :=
  {p | 0 ≤ p.1.1 ∧ 0 ≤ p.1.2 ∧ |p.2| ≤ powerConeGeometricMean α p.1}

namespace PowerCone

/- Source-facing notation for the scalar power cone owner used in Definition 5.4.7.7. -/
scoped notation:max "K_[" α:arg "]" => powerCone α

end PowerCone

open scoped PowerCone

/-- Helper for Definition 5.4.7.7: membership in the scalar power cone is exactly the pair of
coordinate nonnegativity inequalities together with the geometric-mean bound. -/
private theorem mem_powerCone_iff (α x₁ x₂ z : ℝ) :
    ((x₁, x₂), z) ∈ K_[α] ↔
      0 ≤ x₁ ∧ 0 ≤ x₂ ∧ |z| ≤ powerConeGeometricMean α (x₁, x₂) :=
  Iff.rfl

private abbrev liftedPowerConeCoord (τ : ℝ) (x z : Eₙ) (i : Fin n) : ((ℝ × ℝ) × ℝ) :=
  ((x i, τ), z i)

/-- Helper for Definition 5.4.7.7: the interior of `powerConeQ1` is the strict positive orthant
`x₁ > 0`, `x₂ > 0`. -/
private theorem mem_interior_powerConeQ1_iff (x₁ x₂ : ℝ) :
    (x₁, x₂) ∈ interior powerConeQ1 ↔ 0 < x₁ ∧ 0 < x₂ := by
  have hfst :
      interior {p : ℝ × ℝ | 0 ≤ p.1} = {p : ℝ × ℝ | 0 < p.1} := by
    calc
      interior {p : ℝ × ℝ | 0 ≤ p.1}
          = interior ((Prod.fst : ℝ × ℝ → ℝ) ⁻¹' Set.Ici (0 : ℝ)) := by
              rfl
      _ = (Prod.fst : ℝ × ℝ → ℝ) ⁻¹' interior (Set.Ici (0 : ℝ)) := by
            symm
            exact
              isOpenMap_fst.preimage_interior_eq_interior_preimage continuous_fst (Set.Ici (0 : ℝ))
      _ = {p : ℝ × ℝ | 0 < p.1} := by
            ext p
            simp
  have hsnd :
      interior {p : ℝ × ℝ | 0 ≤ p.2} = {p : ℝ × ℝ | 0 < p.2} := by
    calc
      interior {p : ℝ × ℝ | 0 ≤ p.2}
          = interior ((Prod.snd : ℝ × ℝ → ℝ) ⁻¹' Set.Ici (0 : ℝ)) := by
              rfl
      _ = (Prod.snd : ℝ × ℝ → ℝ) ⁻¹' interior (Set.Ici (0 : ℝ)) := by
            symm
            exact
              isOpenMap_snd.preimage_interior_eq_interior_preimage continuous_snd (Set.Ici (0 : ℝ))
      _ = {p : ℝ × ℝ | 0 < p.2} := by
            ext p
            simp
  rw [show powerConeQ1 = {p : ℝ × ℝ | 0 ≤ p.1} ∩ {p : ℝ × ℝ | 0 ≤ p.2} by
      ext p
      rcases p with ⟨y₁, y₂⟩
      simpa [Set.mem_setOf_eq, Set.mem_inter_iff] using (mem_powerConeQ1_iff y₁ y₂),
    interior_inter, hfst, hsnd]
  simp [Set.mem_setOf_eq, Set.mem_inter_iff]

/- Definition 5.4.7.7 lies in the Chapter 5 finite-dimensional `ℓ_p` epigraph / lifted-barrier
domain.

Sampled owner declarations:
* `powerCone` from `Definition_5_4_7_1`, the source-facing symmetric power-cone owner for the
  coordinate triples `((x⁽ⁱ⁾, τ), z⁽ⁱ⁾)`;
* `power_cone_barrier` from `Theorem_5_4_7_3`, the chapter owner of the logarithmic power-cone
  barrier appearing in each summand of `Ψ_α`;
* `logarithmicBarrierDomain` / `LogarithmicBarrierPoint` from `Definition_5_4_5_7`, the chapter
  barrier-owner pattern "strict domain `Set` + subtype carrier + ambient bridge formula";
* `circumscribedEllipsoidBarrierDomain` / `CircumscribedEllipsoidBarrierPoint` from
  `Definition_5_4_5_5`, the same strict-domain pattern for a neighboring logarithmic barrier.

Source/core/bridge triage:
* source-facing: the strict lifted barrier domain `lpEpigraphConeBarrierLiftDomain α` and the
  barrier `lpEpigraphConeBarrierLifted α` on that domain;
* core/canonical: the coordinate owner `power_cone_barrier α` from the earlier power-cone files;
* bridge/view: the ambient finite-sum map `lpEpigraphConeBarrierLiftedAmbient α` and its
  coordinatewise textbook expansion.

Primitive data:
* coordinatewise strict membership in the canonical owner `interior K_[α]`;
* the shared positivity condition `τ > 0`, kept explicit because it is not recoverable from the
  coordinate owner when `n = 0`;
* the normalization equation `∑ i, x⁽ⁱ⁾ = τ`.

Derived API:
* the subtype carrier `LpEpigraphConeBarrierLiftPoint α`;
* the ambient barrier as a sum of the canonical coordinate barriers `power_cone_barrier α`;
* the companion theorem expanding that owner back to the raw textbook logarithmic formula.

This refinement keeps the barrier on its mathematically correct strict lifted domain rather than
on the closed witness set from the previous existence theorem, owns the coordinate strictness via
the earlier power-cone interior `interior K_[α]`, and reuses the chapter power-cone barrier owner
for each coordinate summand instead of duplicating that formula locally.
-/

/-- The lifted domain `𝓗_P` for the `ℓ_p` epigraph cone consists of triples `(τ, x, z)` such that
`x` is coordinatewise nonnegative, the inequalities
`(x^(i))^α τ^(1 - α) ≥ |z^(i)|` hold for every coordinate, and `∑ i, x^(i) = τ`. -/
def lpEpigraphConeLiftDomain (α : ℝ) : Set LpLiftPointₙ :=
  {p |
    (∀ i : Fin n, liftedPowerConeCoord n p.1 p.2.1 p.2.2 i ∈ K_[α]) ∧
      ∑ i : Fin n, p.2.1 i = p.1}

/-- A triple `(τ, x, z)` belongs to `lpEpigraphConeLiftDomain n α` exactly when it satisfies the
coordinatewise lifted `ℓ_p`-epigraph inequalities and the normalization equation
`∑ i, x^(i) = τ`. -/
theorem mem_lpEpigraphConeLiftDomain_iff
    (α τ : ℝ) (x z : Eₙ) :
    (τ, x, z) ∈ lpEpigraphConeLiftDomain n α ↔
      (∀ i : Fin n, 0 ≤ x i) ∧
        (∀ i : Fin n, Real.rpow (x i) α * Real.rpow τ (1 - α) ≥ |z i|) ∧
          ∑ i : Fin n, x i = τ := by
  constructor
  · rintro ⟨hp, hsum⟩
    refine ⟨?_, ?_, hsum⟩
    · intro i
      rcases (mem_powerCone_iff α (x i) τ (z i)).1 (hp i) with ⟨hxi, -, -⟩
      exact hxi
    · intro i
      rcases (mem_powerCone_iff α (x i) τ (z i)).1 (hp i) with ⟨-, -, hzi⟩
      exact hzi
  · rintro ⟨hx, hz, hsum⟩
    refine ⟨?_, hsum⟩
    have hτ : 0 ≤ τ := by
      have hsum_nonneg : 0 ≤ ∑ i : Fin n, x i :=
        Finset.sum_nonneg fun i _ ↦ hx i
      simpa [hsum] using hsum_nonneg
    intro i
    exact (mem_powerCone_iff α (x i) τ (z i)).2 ⟨hx i, hτ, hz i⟩

/-- The strict lifted domain `𝓗_P` on which the lifted `ℓ_p`-epigraph logarithmic barrier is
defined. Its primitive data are coordinatewise strict membership in the canonical power-cone owner
`interior K_[α]`, the shared positivity condition `τ > 0`, and the normalization
`∑ i, x^(i) = τ`. -/
def lpEpigraphConeBarrierLiftDomain (α : ℝ) : Set LpLiftPointₙ :=
  {p |
    (∀ i : Fin n, liftedPowerConeCoord n p.1 p.2.1 p.2.2 i ∈ interior K_[α]) ∧
      0 < p.1 ∧
        (∑ i : Fin n, p.2.1 i) = p.1}

/-- A triple `(τ, x, z)` belongs to `lpEpigraphConeBarrierLiftDomain n α` exactly when each
coordinate lies in `interior K_[α]`, with the shared strictness condition `τ > 0` and the
normalization `∑ i, x^(i) = τ`. -/
theorem mem_lpEpigraphConeBarrierLiftDomain_iff_interior
    (α τ : ℝ) (x z : Eₙ) :
    (τ, x, z) ∈ lpEpigraphConeBarrierLiftDomain n α ↔
      (∀ i : Fin n, liftedPowerConeCoord n τ x z i ∈ interior K_[α]) ∧
        0 < τ ∧
          (∑ i : Fin n, x i) = τ :=
  Iff.rfl

/-- Helper for Definition 5.4.7.7: the interior of `powerConeQ2 = {(y, z) | y ≥ |z|}` is the
strict region `|z| < y`. -/
private theorem mem_interior_powerConeQ2_iff (y z : ℝ) :
    (y, z) ∈ interior powerConeQ2 ↔ |z| < y := by
  constructor
  · intro hmem
    have hle : |z| ≤ y := (mem_powerConeQ2_iff y z).1 (interior_subset hmem)
    by_contra hnot
    have heq : |z| = y := le_antisymm hle (le_of_not_gt hnot)
    let γ : ℝ → ℝ × ℝ := fun s ↦ (s, z)
    have hpre : γ ⁻¹' interior powerConeQ2 ∈ nhds y := by
      exact (show Continuous γ by fun_prop).continuousAt.preimage_mem_nhds <|
        IsOpen.mem_nhds isOpen_interior (by simpa [γ] using hmem)
    rcases Metric.mem_nhds_iff.mp hpre with ⟨ε, hε, hεsub⟩
    have hdown : y - ε / 2 ∈ Metric.ball y ε := by
      rw [Metric.mem_ball, Real.dist_eq, abs_of_neg (by linarith)]
      linarith
    have hbad : (y - ε / 2, z) ∈ powerConeQ2 :=
      interior_subset (hεsub hdown)
    have hbad' : |z| ≤ y - ε / 2 := (mem_powerConeQ2_iff (y - ε / 2) z).1 hbad
    rw [heq] at hbad'
    linarith
  · intro hstrict
    let U : Set (ℝ × ℝ) := {p | |p.2| < p.1}
    have hU_open : IsOpen U := by
      exact isOpen_lt continuous_snd.abs continuous_fst
    have hpU : (y, z) ∈ U := by
      simpa [U] using hstrict
    refine mem_interior_iff_mem_nhds.mpr ?_
    refine Filter.mem_of_superset (hU_open.mem_nhds hpU) ?_
    intro p hp
    exact (mem_powerConeQ2_iff p.1 p.2).2 hp.le

/-- Helper for Definition 5.4.7.7: an interior point of the scalar power cone has positive
coordinates and strict geometric-mean slack. -/
private theorem strict_of_mem_interior_powerConeCoord
    {α x τ z : ℝ} (hmem : ((x, τ), z) ∈ interior K_[α]) :
    0 < x ∧ 0 < τ ∧ |z| < powerConeGeometricMean α (x, τ) := by
  have hsubset :
      K_[α] ⊆ (Prod.fst : ((ℝ × ℝ) × ℝ) → ℝ × ℝ) ⁻¹' powerConeQ1 := by
    intro p hp
    rcases p with ⟨⟨u, v⟩, w⟩
    have hpCone := (mem_powerCone_iff α u v w).1 hp
    exact (mem_powerConeQ1_iff u v).2 ⟨hpCone.1, hpCone.2.1⟩
  have hpreimage :
      ((x, τ), z) ∈ interior ((Prod.fst : ((ℝ × ℝ) × ℝ) → ℝ × ℝ) ⁻¹' powerConeQ1) :=
    interior_mono hsubset hmem
  have hQ1 : (x, τ) ∈ interior powerConeQ1 := by
    change
      ((x, τ), z) ∈
        (Prod.fst : ((ℝ × ℝ) × ℝ) → ℝ × ℝ) ⁻¹' interior powerConeQ1
    rw [←
      isOpenMap_fst.preimage_interior_eq_interior_preimage
        continuous_fst
        powerConeQ1] at hpreimage
    exact hpreimage
  have hcone : ((x, τ), z) ∈ K_[α] := interior_subset hmem
  have hcone_mem := (mem_powerCone_iff α x τ z).1 hcone
  have hx : 0 < x := (mem_interior_powerConeQ1_iff x τ).1 hQ1 |>.1
  have hτ : 0 < τ := (mem_interior_powerConeQ1_iff x τ).1 hQ1 |>.2
  have hz : |z| < powerConeGeometricMean α (x, τ) := by
    by_contra hz_not
    have hz_eq : |z| = powerConeGeometricMean α (x, τ) :=
      le_antisymm hcone_mem.2.2 (le_of_not_gt hz_not)
    let γ : ℝ → ((ℝ × ℝ) × ℝ) := fun s ↦ ((x, τ), s)
    have hpre :
        γ ⁻¹' interior K_[α] ∈ nhds z := by
      exact (show Continuous γ by fun_prop).continuousAt.preimage_mem_nhds <|
        IsOpen.mem_nhds isOpen_interior (by simpa [γ] using hmem)
    rcases Metric.mem_nhds_iff.mp hpre with ⟨ε, hε, hεsub⟩
    by_cases hz_nonneg : 0 ≤ z
    · have hup : z + ε / 2 ∈ Metric.ball z ε := by
        have hhalf_nonneg : 0 ≤ z + ε / 2 - z := by linarith
        rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg hhalf_nonneg]
        linarith
      have hbad : γ (z + ε / 2) ∈ K_[α] := interior_subset (hεsub hup)
      have hbad_mem := (mem_powerCone_iff α x τ (z + ε / 2)).1 hbad
      have habs_shift : |z + ε / 2| = |z| + ε / 2 := by
        rw [abs_of_nonneg (by linarith), abs_of_nonneg hz_nonneg]
      rw [habs_shift, hz_eq] at hbad_mem
      linarith
    · have hz_neg : z < 0 := lt_of_not_ge hz_nonneg
      have hdown : z - ε / 2 ∈ Metric.ball z ε := by
        have hdist : |(z - ε / 2 : ℝ) - z| = ε / 2 := by
          have hneg : z - ε / 2 - z = -(ε / 2) := by ring_nf
          have hhalf_neg : -(ε / 2 : ℝ) < 0 := by
            have hhalf_pos : 0 < (ε / 2 : ℝ) := by positivity
            linarith
          rw [hneg, abs_of_neg hhalf_neg]
          ring_nf
        rw [Metric.mem_ball, Real.dist_eq, hdist]
        linarith
      have hbad : γ (z - ε / 2) ∈ K_[α] := interior_subset (hεsub hdown)
      have hbad_mem := (mem_powerCone_iff α x τ (z - ε / 2)).1 hbad
      have habs_shift : |z - ε / 2| = |z| + ε / 2 := by
        rw [abs_of_neg (by linarith), abs_of_neg hz_neg]
        ring_nf
      rw [habs_shift, hz_eq] at hbad_mem
      linarith
  -- Extract the coordinate positivity first, then rule out the boundary case in the `z` direction.
  exact ⟨hx, hτ, hz⟩

/-- Helper for Definition 5.4.7.7: strict geometric-mean slack is equivalent to positivity of the
textbook squared slack once `x` and `τ` are positive. -/
private theorem strictSlack_iff_sqSlackPos
    {α x τ z : ℝ} (hx : 0 < x) (hτ : 0 < τ) :
    |z| < powerConeGeometricMean α (x, τ) ↔
      0 < Real.rpow x (2 * α) * Real.rpow τ (2 * (1 - α)) - z ^ (2 : ℕ) := by
  have hgeom_pos : 0 < powerConeGeometricMean α (x, τ) := by
    -- Positivity of both bases makes the weighted geometric mean strictly positive.
    rw [powerConeGeometricMean_apply]
    exact mul_pos (Real.rpow_pos_of_pos hx α) (Real.rpow_pos_of_pos hτ (1 - α))
  have hx_sq :
      (Real.rpow x α) ^ (2 : ℕ) = Real.rpow x (2 * α) := by
    calc
      (Real.rpow x α) ^ (2 : ℕ) = Real.rpow x (α * 2) := by
        symm
        simpa using (Real.rpow_mul_natCast (le_of_lt hx) α 2)
      _ = Real.rpow x (2 * α) := by ring_nf
  have hτ_sq :
      (Real.rpow τ (1 - α)) ^ (2 : ℕ) = Real.rpow τ (2 * (1 - α)) := by
    calc
      (Real.rpow τ (1 - α)) ^ (2 : ℕ) = Real.rpow τ ((1 - α) * 2) := by
        symm
        simpa using (Real.rpow_mul_natCast (le_of_lt hτ) (1 - α) 2)
      _ = Real.rpow τ (2 * (1 - α)) := by ring_nf
  have hgeom_sq :
      (powerConeGeometricMean α (x, τ)) ^ (2 : ℕ) =
        Real.rpow x (2 * α) * Real.rpow τ (2 * (1 - α)) := by
    -- Normalize the square of the weighted geometric mean into the textbook `rpow` product.
    rw [powerConeGeometricMean_apply, mul_pow, hx_sq, hτ_sq]
  constructor
  · intro hz
    have hsq_abs_lt :
        |z| ^ (2 : ℕ) < (powerConeGeometricMean α (x, τ)) ^ (2 : ℕ) := by
      nlinarith [hz, abs_nonneg z, hgeom_pos]
    have hsq_lt : z ^ (2 : ℕ) < (powerConeGeometricMean α (x, τ)) ^ (2 : ℕ) := by
      simpa [sq_abs] using hsq_abs_lt
    have hslack : 0 < (powerConeGeometricMean α (x, τ)) ^ (2 : ℕ) - z ^ (2 : ℕ) := by
      linarith
    simpa [hgeom_sq] using hslack
  · intro hz
    have hslack :
        0 < (powerConeGeometricMean α (x, τ)) ^ (2 : ℕ) - z ^ (2 : ℕ) := by
      simpa [hgeom_sq] using hz
    have hsq_lt : z ^ (2 : ℕ) < (powerConeGeometricMean α (x, τ)) ^ (2 : ℕ) := by
      linarith
    have hsq_abs_lt :
        |z| ^ (2 : ℕ) < (powerConeGeometricMean α (x, τ)) ^ (2 : ℕ) := by
      simpa [sq_abs] using hsq_lt
    -- Since the right-hand side is positive, the strict square inequality descends to `|z| < ξ`.
    nlinarith [hsq_abs_lt, abs_nonneg z, hgeom_pos]

/-- Helper for Definition 5.4.7.7: expanding the local coordinate barrier owner recovers the
textbook logarithmic power-cone formula. -/
private theorem powerConeCoordBarrier_apply
    (α x₁ x₂ z : ℝ) :
    power_cone_barrier α ((x₁, x₂), z) =
      -Real.log
          (Real.rpow x₁ (2 * α) * Real.rpow x₂ (2 * (1 - α)) - z ^ (2 : ℕ)) -
        Real.log x₁ - Real.log x₂ := by
  rfl

/-- Helper for Definition 5.4.7.7: positive orthant coordinates together with strict
geometric-mean slack place the scalar triple in `interior K_[α]`. -/
private theorem mem_interior_powerConeCoord_of_strict
    {α x τ z : ℝ} (hx : 0 < x) (hτ : 0 < τ)
    (hz : |z| < powerConeGeometricMean α (x, τ)) :
    ((x, τ), z) ∈ interior K_[α] := by
  let p0 : ((ℝ × ℝ) × ℝ) := ((x, τ), z)
  let slack : ((ℝ × ℝ) × ℝ) → ℝ :=
    fun p ↦ powerConeGeometricMean α p.1 - |p.2|
  have hx_mem : {p : ((ℝ × ℝ) × ℝ) | 0 < p.1.1} ∈ nhds p0 := by
    exact continuous_fst.fst.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hx)
  have hτ_mem : {p : ((ℝ × ℝ) × ℝ) | 0 < p.1.2} ∈ nhds p0 := by
    exact continuous_fst.snd.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hτ)
  have hslack_cont : ContinuousAt slack p0 := by
    have hx_cont :
        ContinuousAt (fun p : ((ℝ × ℝ) × ℝ) ↦ Real.rpow p.1.1 α) p0 :=
      (continuous_fst.fst.continuousAt).rpow_const (Or.inl hx.ne')
    have hτ_cont :
        ContinuousAt (fun p : ((ℝ × ℝ) × ℝ) ↦ Real.rpow p.1.2 (1 - α)) p0 :=
      (continuous_fst.snd.continuousAt).rpow_const (Or.inl hτ.ne')
    have habs_cont : ContinuousAt (fun p : ((ℝ × ℝ) × ℝ) ↦ |p.2|) p0 :=
      continuous_snd.continuousAt.abs
    simpa [slack, powerConeGeometricMean] using hx_cont.mul hτ_cont |>.sub habs_cont
  have hslack_mem : {p : ((ℝ × ℝ) × ℝ) | 0 < slack p} ∈ nhds p0 := by
    have hslack0 : 0 < slack p0 := by
      simpa [p0, slack] using sub_pos.mpr hz
    exact hslack_cont.preimage_mem_nhds (Ioi_mem_nhds hslack0)
  have hmem :
      {p : ((ℝ × ℝ) × ℝ) | 0 < p.1.1} ∩
        ({p : ((ℝ × ℝ) × ℝ) | 0 < p.1.2} ∩
          {p : ((ℝ × ℝ) × ℝ) | 0 < slack p}) ∈ nhds p0 := by
    exact Filter.inter_mem hx_mem (Filter.inter_mem hτ_mem hslack_mem)
  refine mem_interior_iff_mem_nhds.mpr ?_
  refine Filter.mem_of_superset hmem ?_
  intro p hp
  rcases hp with ⟨hx', hp⟩
  rcases hp with ⟨hτ', hslack'⟩
  have hslack'' : 0 < slack p := hslack'
  -- The neighborhood already enforces the positive coordinates and strict slack inequality.
  refine (mem_powerCone_iff α p.1.1 p.1.2 p.2).2 ?_
  refine ⟨le_of_lt hx', le_of_lt hτ', ?_⟩
  simpa [slack, sub_nonneg] using hslack''.le

/-- Definition 5.4.7.7: expanding the owner `interior K_[α]` rewrites strict lifted-domain
membership back to the coordinatewise positivity conditions from the textbook definition. -/
theorem mem_lpEpigraphConeBarrierLiftDomain_iff
    (α τ : ℝ) (x z : Eₙ) :
    (τ, x, z) ∈ lpEpigraphConeBarrierLiftDomain n α ↔
      (∀ i : Fin n, 0 < x i) ∧
        0 < τ ∧
          (∀ i : Fin n,
            0 < Real.rpow (x i) (2 * α) * Real.rpow τ (2 * (1 - α)) - (z i) ^ (2 : ℕ)) ∧
            (∑ i : Fin n, x i) = τ := by
  rw [mem_lpEpigraphConeBarrierLiftDomain_iff_interior]
  constructor
  · rintro ⟨hcoord, hτ, hsum⟩
    refine ⟨?_, hτ, ?_, hsum⟩
    · intro i
      -- Read each coordinate of the strict lifted domain through the scalar interior criterion.
      have hstrict :
          0 < x i ∧ 0 < τ ∧ |z i| < powerConeGeometricMean α (x i, τ) :=
        strict_of_mem_interior_powerConeCoord
          (α := α)
          (hmem := by simpa [liftedPowerConeCoord] using hcoord i)
      exact hstrict.1
    · intro i
      -- Convert strict geometric-mean slack to the squared-slack formula used in this file.
      have hstrict :
          0 < x i ∧ 0 < τ ∧ |z i| < powerConeGeometricMean α (x i, τ) :=
        strict_of_mem_interior_powerConeCoord
          (α := α)
          (hmem := by simpa [liftedPowerConeCoord] using hcoord i)
      exact (strictSlack_iff_sqSlackPos (α := α) hstrict.1 hstrict.2.1).1 hstrict.2.2
  · rintro ⟨hx, hτ, hslack, hsum⟩
    refine ⟨?_, hτ, hsum⟩
    intro i
    have hstrict : |z i| < powerConeGeometricMean α (x i, τ) :=
      (strictSlack_iff_sqSlackPos (α := α) (hx i) hτ).2 (hslack i)
    -- Rebuild each coordinate of the lifted tuple as an interior point of `K_[α]`.
    simpa [liftedPowerConeCoord] using
      mem_interior_powerConeCoord_of_strict
        (α := α)
        (hx := hx i)
        (hτ := hτ)
        (hz := hstrict)

/-- The subtype of points in the strict lifted `ℓ_p`-epigraph barrier domain. This is the natural
owner carrier for Definition 5.4.7.7. -/
abbrev LpEpigraphConeBarrierLiftPoint (α : ℝ) :=
  {p : LpLiftPointₙ // p ∈ lpEpigraphConeBarrierLiftDomain n α}

/-- The ambient lifted barrier is the finite sum of the canonical Chapter 5 power-cone barriers on
the coordinate triples `((x^(i), τ), z^(i))`. The barrier itself is obtained by restricting this
ambient map to `LpEpigraphConeBarrierLiftPoint n α`. -/
def lpEpigraphConeBarrierLiftedAmbient (α : ℝ) : LpLiftPointₙ → ℝ
  | (τ, x, z) => ∑ i : Fin n, power_cone_barrier α (liftedPowerConeCoord n τ x z i)

/-- The barrier `Ψ_α` on the strict lifted domain `𝓗_P` is the restriction of the ambient
coordinatewise power-cone barrier sum. -/
def lpEpigraphConeBarrierLifted (α : ℝ) : LpEpigraphConeBarrierLiftPoint n α → ℝ :=
  fun p ↦ lpEpigraphConeBarrierLiftedAmbient n α p.1

/-- Evaluating the ambient lifted `ℓ_p`-epigraph barrier at `(τ, x, z)` is exactly the sum of the
canonical coordinate power-cone barriers. -/
theorem lpEpigraphConeBarrierLiftedAmbient_apply
    (α τ : ℝ) (x z : Eₙ) :
    lpEpigraphConeBarrierLiftedAmbient n α (τ, x, z) =
      ∑ i : Fin n, power_cone_barrier α (liftedPowerConeCoord n τ x z i) :=
  rfl

/-- Expanding the coordinate barrier owner `power_cone_barrier α` rewrites the ambient lifted
barrier back to the textbook logarithmic formula for `Ψ_α(τ, x, z)`. -/
theorem lpEpigraphConeBarrierLiftedAmbient_apply_formula
    (α τ : ℝ) (x z : Eₙ) (hτ : 0 ≤ τ) (hx : ∀ i : Fin n, 0 ≤ x i) :
    lpEpigraphConeBarrierLiftedAmbient n α (τ, x, z) =
      -∑ i : Fin n,
        (Real.log
            (Real.rpow (x i) (2 * α) * Real.rpow τ (2 * (1 - α)) - (z i) ^ (2 : ℕ)) +
          Real.log (x i) + Real.log τ) := by
  let _ := hτ
  let _ := hx
  unfold lpEpigraphConeBarrierLiftedAmbient
  calc
    ∑ i : Fin n, power_cone_barrier α (liftedPowerConeCoord n τ x z i)
      = ∑ i : Fin n,
          (-(Real.log
              (Real.rpow (x i) (2 * α) * Real.rpow τ (2 * (1 - α)) - (z i) ^ (2 : ℕ)) +
            Real.log (x i) + Real.log τ)) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [powerConeCoordBarrier_apply α (x i) τ (z i)]
          ring_nf
    _ = -∑ i : Fin n,
          (Real.log
              (Real.rpow (x i) (2 * α) * Real.rpow τ (2 * (1 - α)) - (z i) ^ (2 : ℕ)) +
            Real.log (x i) + Real.log τ) := by
          rw [Finset.sum_neg_distrib]

/-- Evaluating `lpEpigraphConeBarrierLifted n α` on a strict-domain point agrees with the ambient
bridge formula. -/
@[simp] theorem lpEpigraphConeBarrierLifted_apply
    (α : ℝ) (p : LpEpigraphConeBarrierLiftPoint n α) :
    lpEpigraphConeBarrierLifted n α p =
      lpEpigraphConeBarrierLiftedAmbient n α p :=
  rfl

/-- At a strict lifted-domain triple `(τ, x, z)`, the barrier `lpEpigraphConeBarrierLifted n α`
is the sum of the canonical coordinate power-cone barriers. -/
theorem lpEpigraphConeBarrierLifted_apply_triple
    (α τ : ℝ) (x z : Eₙ)
    (h : (τ, x, z) ∈ lpEpigraphConeBarrierLiftDomain n α) :
    lpEpigraphConeBarrierLifted n α ⟨(τ, x, z), h⟩ =
      ∑ i : Fin n, power_cone_barrier α (liftedPowerConeCoord n τ x z i) :=
  rfl

/-- At a strict lifted-domain triple `(τ, x, z)`, the barrier `lpEpigraphConeBarrierLifted n α`
recovers the textbook finite-sum formula for `Ψ_α(τ, x, z)`. -/
theorem lpEpigraphConeBarrierLifted_apply_triple_formula
    (α τ : ℝ) (x z : Eₙ)
    (h : (τ, x, z) ∈ lpEpigraphConeBarrierLiftDomain n α) :
    lpEpigraphConeBarrierLifted n α ⟨(τ, x, z), h⟩ =
      -∑ i : Fin n,
        (Real.log
            (Real.rpow (x i) (2 * α) * Real.rpow τ (2 * (1 - α)) - (z i) ^ (2 : ℕ)) +
          Real.log (x i) + Real.log τ) := by
  rw [mem_lpEpigraphConeBarrierLiftDomain_iff] at h
  have hx : ∀ i : Fin n, 0 ≤ x i := fun i ↦ (h.1 i).le
  have hτ : 0 ≤ τ := h.2.1.le
  simpa [lpEpigraphConeBarrierLifted] using
    lpEpigraphConeBarrierLiftedAmbient_apply_formula n α τ x z hτ hx

end

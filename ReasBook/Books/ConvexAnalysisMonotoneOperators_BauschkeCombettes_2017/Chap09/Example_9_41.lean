/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Example_9_35
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Proposition_9_40
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Remark_9_37

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open Filter Set
open scoped BigOperators
open scoped Topology

universe u

namespace ERealFunction

attribute [local instance] Classical.propDecidable

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}

namespace Example941EntropyCopy

/-- Helper for Example 9.41: the `]-∞,+∞]`-valued entropy integrand `x ↦ x \log x - x` on the
nonnegative half-line, extended by `0` at the origin and by `+∞` on negative inputs. -/
noncomputable def boltzmannEntropy : ℝ → Set.Ioi (⊥ : EReal) :=
  fun x ↦
    if 0 < x then
      ⟨((x * Real.log x - x : ℝ) : EReal), EReal.bot_lt_coe _⟩
    else if x = 0 then
      ⟨(0 : EReal), EReal.bot_lt_coe 0⟩
    else
      ⟨(⊤ : EReal), Set.mem_Ioi.mpr bot_lt_top⟩

/-- Helper for Example 9.41: on `(0,+∞)`, the entropy integrand is the real formula
`x \log x - x`. -/
@[simp] theorem boltzmannEntropy_apply_of_pos {x : ℝ} (hx : 0 < x) :
    (boltzmannEntropy x : EReal) = ((x * Real.log x - x : ℝ) : EReal) := by
  -- The positive branch of the entropy integrand is active.
  simp [boltzmannEntropy, hx]

/-- Helper for Example 9.41: at `0`, the entropy integrand takes the value `0`. -/
@[simp] theorem boltzmannEntropy_apply_zero :
    (boltzmannEntropy 0 : EReal) = 0 := by
  -- The middle branch of the piecewise definition handles the origin.
  simp [boltzmannEntropy]

/-- Helper for Example 9.41: on `(-∞,0)`, the entropy integrand takes the value `+∞`. -/
@[simp] theorem boltzmannEntropy_apply_of_neg {x : ℝ} (hx : x < 0) :
    (boltzmannEntropy x : EReal) = ⊤ := by
  -- Negative inputs land in the final `+∞` branch.
  simp [boltzmannEntropy, not_lt.mpr hx.le, hx.ne]

/-- Helper for Example 9.41: nonnegative inputs all use the finite real entropy formula. -/
@[simp] theorem boltzmannEntropy_apply_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    (boltzmannEntropy x : EReal) = ((x * Real.log x - x : ℝ) : EReal) := by
  -- Split the boundary case `x = 0` from the genuinely positive branch.
  by_cases hx0 : x = 0
  · subst hx0
    simp
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    exact boltzmannEntropy_apply_of_pos hxpos

/-- Helper for Example 9.41: the effective domain of the scalar entropy integrand is the closed
half-line `[0,+∞)`. -/
theorem effectiveDomain_boltzmannEntropy :
    effectiveDomain boltzmannEntropy = Set.Ici (0 : ℝ) := by
  ext x
  constructor
  · intro hx
    by_cases hxneg : x < 0
    · -- Negative inputs are excluded because their value is `+∞`.
      have htop : (boltzmannEntropy x : EReal) = ⊤ := boltzmannEntropy_apply_of_neg hxneg
      rw [mem_effectiveDomain_iff, htop] at hx
      exact False.elim ((lt_irrefl (⊤ : EReal)) hx)
    · -- Every remaining point is nonnegative.
      exact le_of_not_gt hxneg
  · intro hx
    rw [mem_effectiveDomain_iff]
    by_cases hx0 : x = 0
    · -- At the origin, the value is exactly `0`.
      simp [hx0]
    · -- Positive inputs use the finite real branch.
      have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
      simpa [boltzmannEntropy_apply_of_pos hxpos] using
        (EReal.coe_lt_top (x * Real.log x - x))

/-- Helper for Example 9.41: the scalar entropy integrand is proper as an `EReal`-valued
function. -/
theorem boltzmannEntropy_isProper :
    IsProper (fun x : ℝ ↦ (boltzmannEntropy x : EReal)) := by
  refine ⟨?_, ⟨0, ?_⟩⟩
  · -- The subtype codomain `]-∞,+∞]` rules out the value `-∞`.
    intro x
    exact ne_of_gt (show (⊥ : EReal) < (boltzmannEntropy x : EReal) from (boltzmannEntropy x).2)
  · -- The origin belongs to the ordinary domain because the value there is finite.
    simp [dom, boltzmannEntropy]

/-- Helper for Example 9.41: a proper strictly convex `]-∞,+∞]`-valued function is convex on its
effective domain. -/
private theorem convexOn_effectiveDomain_of_strictlyConvex
    {g : ℝ → Set.Ioi (⊥ : EReal)}
    (hproper : IsProper (fun x : ℝ ↦ (g x : EReal))) (hg : StrictlyConvex g) :
    ConvexOn g (effectiveDomain g) := by
  refine ⟨hproper.2, subset_rfl, ?_⟩
  intro x hx y hy α hα0 hα1
  by_cases hxy : x = y
  · -- Equal endpoints collapse the strict Jensen expression to equality.
    subst y
    have hcombo : α • x + (1 - α) • x = x := by
      calc
        α • x + (1 - α) • x = (α + (1 - α)) • x := by rw [add_smul]
        _ = x := by simp
    have hα_nonneg : 0 ≤ (α : EReal) := by
      exact_mod_cast hα0.le
    have hβ_nonneg : 0 ≤ ((1 - α : ℝ) : EReal) := by
      exact_mod_cast (sub_nonneg.mpr hα1.le)
    have hsum : (α : EReal) + (1 - α : EReal) = 1 := by
      have hsum_real : α + (1 - α : ℝ) = 1 := by
        ring
      exact_mod_cast hsum_real
    have hweight :
        (α : EReal) * (g x : EReal) + (1 - α : EReal) * (g x : EReal) = (g x : EReal) := by
      calc
        (α : EReal) * (g x : EReal) + (1 - α : EReal) * (g x : EReal)
            = ((α : EReal) + (1 - α : EReal)) * (g x : EReal) := by
                symm
                exact EReal.right_distrib_of_nonneg hα_nonneg hβ_nonneg
        _ = (g x : EReal) := by rw [hsum, one_mul]
    have hvalue : (g (α • x + (1 - α) • x) : EReal) = (g x : EReal) := by
      exact congrArg (fun t : ℝ ↦ (g t : EReal)) hcombo
    calc
      (g (α • x + (1 - α) • x) : EReal) = (g x : EReal) := hvalue
      _ ≤ (α : EReal) * (g x : EReal) + (1 - α : EReal) * (g x : EReal) := by
        rw [hweight]
  · -- Distinct points satisfy the stronger strict Jensen inequality.
    exact le_of_lt (hg.ineq hx hy hxy hα0 hα1)

/-- Helper for Example 9.41: the scalar entropy integrand is lower semicontinuous on `ℝ`. -/
theorem boltzmannEntropy_lowerSemicontinuous :
    LowerSemicontinuous (fun x : ℝ ↦ (boltzmannEntropy x : EReal)) := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro a
  by_cases ha_top : a = ⊤
  · -- The top sublevel set is all of `ℝ`.
    subst ha_top
    simp
  · have htop_not_le : ¬ (⊤ : EReal) ≤ a := by
      intro h
      exact ha_top (le_antisymm le_top h)
    have hpreimage :
        (fun x : ℝ ↦ (boltzmannEntropy x : EReal)) ⁻¹' Set.Iic a =
          Set.Ici (0 : ℝ) ∩
            (fun x : ℝ ↦ ((x * Real.log x - x : ℝ) : EReal)) ⁻¹' Set.Iic a := by
      ext x
      constructor
      · intro hx
        have hx_le : (boltzmannEntropy x : EReal) ≤ a := hx
        have hx_nonneg : 0 ≤ x := by
          by_cases hxneg : x < 0
          · have htop : (boltzmannEntropy x : EReal) = ⊤ := boltzmannEntropy_apply_of_neg hxneg
            exact False.elim (htop_not_le (htop ▸ hx_le))
          · exact le_of_not_gt hxneg
        constructor
        · exact hx_nonneg
        · simpa [boltzmannEntropy_apply_of_nonneg hx_nonneg] using hx_le
      · rintro ⟨hx_nonneg, hx_le⟩
        simpa [boltzmannEntropy_apply_of_nonneg hx_nonneg] using hx_le
    rw [hpreimage]
    have hcont : Continuous fun x : ℝ ↦ ((x * Real.log x - x : ℝ) : EReal) := by
      -- The finite branch is continuous as a real function, then after coercion to `EReal`.
      exact continuous_coe_real_ereal.comp (Real.continuous_mul_log.sub continuous_id)
    exact isClosed_Ici.inter (isClosed_Iic.preimage hcont)

/-- Helper for Example 9.41: the scalar entropy integrand is strictly convex on its effective
domain `[0,+∞)`. -/
theorem boltzmannEntropy_strictlyConvex :
    StrictlyConvex boltzmannEntropy := by
  have hreal :
      StrictConvexOn ℝ (Set.Ici (0 : ℝ)) (fun x ↦ x * Real.log x - x) := by
    -- Route correction: rewrite the entropy branch as `klFun - 1` and reuse mathlib's theorem.
    have hkl :
        StrictConvexOn ℝ (Set.Ici (0 : ℝ)) (fun x ↦ InformationTheory.klFun x - 1) := by
      simpa [sub_eq_add_neg] using InformationTheory.strictConvexOn_klFun.add_const (-1 : ℝ)
    refine hkl.congr ?_
    intro x hx
    change InformationTheory.klFun x - 1 = x * Real.log x - x
    rw [InformationTheory.klFun_apply]
    ring
  intro x hx y hy hxy α hα0 hα1
  have hx_nonneg : x ∈ Set.Ici (0 : ℝ) := by
    simpa [effectiveDomain_boltzmannEntropy] using hx
  have hy_nonneg : y ∈ Set.Ici (0 : ℝ) := by
    simpa [effectiveDomain_boltzmannEntropy] using hy
  have hx0 : 0 ≤ x := hx_nonneg
  have hy0 : 0 ≤ y := hy_nonneg
  have hβ0 : 0 < 1 - α := by
    linarith
  have hsum : α + (1 - α) = 1 := by
    ring
  have hcombo_nonneg : 0 ≤ α • x + (1 - α) • y := by
    change 0 ≤ α * x + (1 - α) * y
    nlinarith
  have hreal_ineq :
      ((α • x + (1 - α) • y) * Real.log (α • x + (1 - α) • y) -
          (α • x + (1 - α) • y) : ℝ) <
        α * (x * Real.log x - x) + (1 - α) * (y * Real.log y - y) := by
    simpa [smul_eq_mul] using hreal.2 hx_nonneg hy_nonneg hxy hα0 hβ0 hsum
  have hineq_ereal :
      ((((α • x + (1 - α) • y) * Real.log (α • x + (1 - α) • y) -
          (α • x + (1 - α) • y) : ℝ)) : EReal) <
        (α : EReal) * (((x * Real.log x - x : ℝ)) : EReal) +
          (1 - α : EReal) * (((y * Real.log y - y : ℝ)) : EReal) := by
    -- Cast the strict real Jensen inequality into `EReal`.
    exact_mod_cast hreal_ineq
  calc
    (boltzmannEntropy (α • x + (1 - α) • y) : EReal)
        = ((((α • x + (1 - α) • y) * Real.log (α • x + (1 - α) • y) -
            (α • x + (1 - α) • y) : ℝ)) : EReal) := by
              simpa using boltzmannEntropy_apply_of_nonneg hcombo_nonneg
    _ < (α : EReal) * (((x * Real.log x - x : ℝ)) : EReal) +
          (1 - α : EReal) * (((y * Real.log y - y : ℝ)) : EReal) :=
        hineq_ereal
    _ = (α : EReal) * (boltzmannEntropy x : EReal) +
          (1 - α : EReal) * (boltzmannEntropy y : EReal) := by
          simp [boltzmannEntropy_apply_of_nonneg hx_nonneg, boltzmannEntropy_apply_of_nonneg hy_nonneg]

/-- Helper for Example 9.41: the scalar entropy integrand belongs to `Γ₀(ℝ)`. -/
theorem boltzmannEntropy_mem_gammaZero :
    boltzmannEntropy ∈ Γ₀(ℝ) := by
  -- Route correction: avoid the blocked `Example_9_35` import by proving lower semicontinuity and
  -- convexity directly from the scalar branch on `[0,+∞)`.
  rw [mem_gammaZero_iff]
  constructor
  · exact boltzmannEntropy_lowerSemicontinuous
  · exact convexOn_effectiveDomain_of_strictlyConvex
      boltzmannEntropy_isProper boltzmannEntropy_strictlyConvex

end Example941EntropyCopy

/-- Nonnegative inputs use the finite real branch of the canonical Boltzmann entropy. -/
@[simp] theorem boltzmannEntropy_apply_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    (boltzmannEntropy x : EReal) = ((x * Real.log x - x : ℝ) : EReal) := by
  rcases hx.eq_or_lt with rfl | hxpos
  · simp
  · exact boltzmannEntropy_apply_of_pos hxpos

/-- Helper for Example 9.41: a finite sum of real `EReal` casts is the cast of the real sum. -/
theorem finset_sum_coe_real_entropy {ι : Type*} (s : Finset ι) (r : ι → ℝ) :
    s.sum (fun i => ((r i : ℝ) : EReal)) = ((((s.sum fun i => r i) : ℝ)) : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi ih =>
      -- Peel off the distinguished summand and use the additive compatibility of `EReal` casts.
      rw [Finset.sum_insert hi, Finset.sum_insert hi, ih, EReal.coe_add]

/-- Helper for Example 9.41: a finite sum of terms in `]-∞,+∞]` never reaches `-∞`. -/
private theorem finset_sum_ne_bot_of_forall_ne_bot_entropy
    {ι : Type*} (s : Finset ι) (g : ι → EReal) (hg : ∀ i ∈ s, g i ≠ ⊥) :
    s.sum g ≠ ⊥ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi ih =>
      -- Isolate the inserted summand and combine the non-`⊥` facts additively.
      rw [Finset.sum_insert hi, EReal.add_ne_bot_iff]
      constructor
      · exact hg i (Finset.mem_insert_self i s)
      · exact ih (fun j hj ↦ hg j (Finset.mem_insert_of_mem hj))

/-- Helper for Example 9.41: one `+∞` summand forces the whole finite entropy sum to be `+∞`. -/
theorem finset_sum_eq_top_of_mem_eq_top_entropy
    {ι : Type*} (s : Finset ι) (a : ι → Set.Ioi (⊥ : EReal)) {i : ι}
    (hi : i ∈ s) (hai : (a i : EReal) = ⊤) :
    s.sum (fun j => (a j : EReal)) = ⊤ := by
  classical
  -- Isolate the `+∞` summand and then absorb the finite remainder into `⊤`.
  calc
    s.sum (fun j => (a j : EReal)) = (a i : EReal) + (s.erase i).sum (fun j => (a j : EReal)) := by
      symm
      exact Finset.add_sum_erase s (fun j ↦ (a j : EReal)) hi
    _ = ⊤ + (s.erase i).sum (fun j => (a j : EReal)) := by
      rw [hai]
    _ = ⊤ := by
      have hsum_ne_bot : (s.erase i).sum (fun j => (a j : EReal)) ≠ ⊥ :=
        finset_sum_ne_bot_of_forall_ne_bot_entropy (s.erase i) (fun j ↦ (a j : EReal))
          (fun j hj ↦ (a j).2.ne')
      simpa using EReal.top_add_of_ne_bot hsum_ne_bot

/-- Helper for Example 9.41: the canonical continuous linear equivalence from the coordinate model
`Fin N → ℝ` to the `lp` owner space used by the finite direct-sum theorem. -/
noncomputable def coordinate_to_lp_equiv (N : ℕ) : (Fin N → ℝ) ≃L[ℝ] lp (fun _ : Fin N ↦ ℝ) 2 :=
  ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin N ↦ ℝ)).symm.trans
    ((lpPiLpₗᵢ (fun _ : Fin N ↦ ℝ) ℝ).symm.toContinuousLinearEquiv))

/-- Helper for Example 9.41: the bundled coordinate equivalence agrees with the unbundled map used
in `discreteEntropy`. -/
theorem coordinate_to_lp_equiv_eq_discrete_map (N : ℕ) (x : Fin N → ℝ) :
    coordinate_to_lp_equiv N x = Equiv.lpPiLp.symm (WithLp.toLp 2 x) := by
  -- Both maps are coordinatewise the identity from the Euclidean model to `lp`.
  ext i
  rfl

/-- The discrete entropy on `ℝ^N`, expressed on the canonical coordinate model `Fin N → ℝ`, as the
pullback of the chapter's finite direct-sum owner along the canonical `WithLp` equivalence. -/
noncomputable def discreteEntropy (N : ℕ) : (Fin N → ℝ) → Set.Ioi (⊥ : EReal) :=
  fun x ↦
    directSumFunction (fun _ : Fin N ↦ boltzmannEntropy) (Equiv.lpPiLp.symm (WithLp.toLp 2 x))

/-- Coercing `discreteEntropy N` to `EReal` recovers the canonical coordinate sum of the scalar
entropy integrand `boltzmannEntropy`. -/
@[simp] theorem discreteEntropy_apply (N : ℕ) (x : Fin N → ℝ) :
    (discreteEntropy N x : EReal) = ∑ i, (boltzmannEntropy (x i) : EReal) := by
  let y : Fin N → ℝ :=
    ((Equiv.lpPiLp.symm (WithLp.toLp 2 x) : lp (fun _ : Fin N ↦ ℝ) 2) : Fin N → ℝ)
  have hy : y = x := by
    ext i
    rfl
  calc
    (discreteEntropy N x : EReal) = ∑ i, (boltzmannEntropy (y i) : EReal) := by
      simp [discreteEntropy, directSumFunction_apply, y]
    _ = ∑ i, (boltzmannEntropy (x i) : EReal) := by
      simp [hy]

-- Proof sketch: expand the canonical coordinate sum from `discreteEntropy_apply` with the branch
-- formulas for `boltzmannEntropy`. If every coordinate is nonnegative, each summand is finite and
-- the sum reduces to the real formula `∑ i, (x i log (x i) - x i)`. If some coordinate is
-- negative, the corresponding summand is `⊤`, so the whole sum is `⊤`.
/-- The coordinate-sum definition of `discreteEntropy` is equivalent to the textbook explicit
formula. -/
theorem discreteEntropy_eq_textbook_formula (N : ℕ) (x : Fin N → ℝ) :
    (discreteEntropy N x : EReal) =
      if ∀ i, 0 ≤ x i then
        ((((∑ i, (x i * Real.log (x i) - x i)) : ℝ)) : EReal)
      else
        ⊤ := by
  by_cases hnonneg : ∀ i, 0 ≤ x i
  · -- Every coordinate is finite, so rewrite each summand and collapse the casted finite sum.
    rw [if_pos hnonneg, discreteEntropy_apply]
    calc
      ∑ i, (boltzmannEntropy (x i) : EReal)
          = ∑ i, (((x i * Real.log (x i) - x i : ℝ) : EReal)) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              simp [boltzmannEntropy_apply_of_nonneg (hnonneg i)]
      _ = ((((∑ i, (x i * Real.log (x i) - x i)) : ℝ)) : EReal) := by
            simpa using finset_sum_coe_real_entropy (s := Finset.univ)
              (r := fun i : Fin N ↦ x i * Real.log (x i) - x i)
  · -- One negative coordinate gives a `⊤` summand, which forces the whole finite sum to be `⊤`.
    rw [if_neg hnonneg, discreteEntropy_apply]
    obtain ⟨i, hi_not_nonneg⟩ := not_forall.mp hnonneg
    have hi_neg : x i < 0 := lt_of_not_ge hi_not_nonneg
    have hi_univ : i ∈ (Finset.univ : Finset (Fin N)) := by
      simp
    exact finset_sum_eq_top_of_mem_eq_top_entropy (s := Finset.univ)
      (a := fun j : Fin N ↦ boltzmannEntropy (x j)) (hi := hi_univ)
      (hai := boltzmannEntropy_apply_of_neg hi_neg)

-- Proof sketch: Example 9.35 gives `boltzmannEntropy ∈ Γ₀(ℝ)`. Apply Proposition 9.40(i) to the
-- integrand `boltzmannEntropy`, using the finite-measure hypothesis as the left disjunct in the
-- proposition's assumption.
/-- Example 9.41: on a finite measure space, the integral functional induced by the entropy
integrand `t ↦ t \log t - t` on `[0,+∞)` belongs to `Γ₀(L²((Ω,\mathcal F,\mu); \mathbb R))`. -/
theorem boltzmannEntropy_integralFunctional_mem_gammaZero
    (hμ : μ Set.univ < ⊤) :
    integralFunctional μ boltzmannEntropy ∈ Γ₀(Ω →₂[μ] ℝ) := by
  -- Route correction: reuse Proposition 9.40 directly once the scalar `Γ₀` owner is available.
  simpa using integralFunctional_mem_gammaZero μ boltzmannEntropy
    boltzmannEntropy_mem_gammaZero (Or.inl hμ)

-- Proof sketch: a probability measure is finite, so specialize
-- `boltzmannEntropy_integralFunctional_mem_gammaZero` to the induced finite-measure hypothesis.
/-- For a probability measure, the entropy integral functional belongs to
`Γ₀(L²((Ω,\mathcal F,\mu); \mathbb R))`. -/
theorem boltzmannEntropy_integralFunctional_mem_gammaZero_of_isProbabilityMeasure
    [IsProbabilityMeasure μ] :
    integralFunctional μ boltzmannEntropy ∈ Γ₀(Ω →₂[μ] ℝ) := by
  -- A probability measure is finite, so the previous theorem applies immediately.
  apply boltzmannEntropy_integralFunctional_mem_gammaZero
  simp [MeasureTheory.measure_univ]

/-- Helper for Example 9.41: the finite direct-sum entropy owner pulled back to the coordinate
model still belongs to `Γ₀`. -/
theorem discreteEntropy_pullback_mem_gammaZero (N : ℕ) :
    (fun x : Fin N → ℝ =>
      directSumFunction (fun _ : Fin N => boltzmannEntropy) (coordinate_to_lp_equiv N x)) ∈
      Γ₀(Fin N → ℝ) := by
  -- First obtain the `Γ₀` owner on `lp`, then pull it back along the coordinate equivalence.
  exact mem_gammaZero_comp_continuousLinearEquiv
    (directSumFunction_mem_gammaZero_of_forall_mem_gammaZero
      (f := fun _ : Fin N ↦ boltzmannEntropy)
      (hf := fun _ ↦ boltzmannEntropy_mem_gammaZero))
    (coordinate_to_lp_equiv N)

-- Proof sketch: identify the canonical `Fin N → ℝ` model of `ℝ^N` with the `L²` space over the
-- finite counting measure on `Fin N`, and then specialize the entropy-integral result to this
-- finite discrete measure space.
/-- The discrete entropy on the canonical `Fin N → ℝ` model of `ℝ^N` belongs to `Γ₀(ℝ^N)`. -/
theorem discreteEntropy_mem_gammaZero (N : ℕ) :
    discreteEntropy N ∈ Γ₀(Fin N → ℝ) := by
  have hEq :
      discreteEntropy N =
        fun x : Fin N → ℝ =>
          directSumFunction (fun _ : Fin N ↦ boltzmannEntropy) (coordinate_to_lp_equiv N x) := by
    -- The two presentations use the same canonical coordinate map into the `lp` owner space.
    funext x
    apply Subtype.ext
    simp [discreteEntropy, coordinate_to_lp_equiv_eq_discrete_map]
  simpa [hEq] using discreteEntropy_pullback_mem_gammaZero N

end ERealFunction

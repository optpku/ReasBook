/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Proposition_8_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

universe u v

namespace ERealFunction

variable {H : Type u} [AddCommGroup H] [Module ℝ H]

omit [AddCommGroup H] [Module ℝ H] in
/-- Helper for Corrollary 8.12: every effective-domain point admits a real height above the
function value. -/
private lemma exists_real_ge_of_mem_dom (f : H → EReal) {x : H} (hx : x ∈ dom f) :
    ∃ ξ : ℝ, f x ≤ (ξ : EReal) := by
  -- Domain membership means that the value lies strictly below `+∞`, so a real separator exists.
  rw [mem_dom_iff] at hx
  rcases EReal.lt_iff_exists_real_btwn.mp hx with ⟨ξ, hξ, _⟩
  exact ⟨ξ, le_of_lt hξ⟩

/-- Helper for Corrollary 8.12: convexity of the epigraph is preserved under finite weighted sums
of real-height epigraph points. -/
private lemma weighted_sum_mem_epigraph_of_convex_epigraph (f : H → EReal)
    (hconv : Convex ℝ (epigraph f)) {ι : Type v} (s : Finset ι) (α : ι → ℝ) (x : ι → H)
    (ξ : ι → ℝ) (hα_nonneg : ∀ i ∈ s, 0 ≤ α i) (hα_sum : ∑ i ∈ s, α i = 1)
    (hξ : ∀ i ∈ s, f (x i) ≤ (ξ i : EReal)) :
    f (∑ i ∈ s, α i • x i) ≤ ((∑ i ∈ s, α i * ξ i : ℝ) : EReal) := by
  have hmem : ∀ i ∈ s, (x i, ξ i) ∈ epigraph f := by
    -- Each chosen real height places the corresponding point in the epigraph.
    intro i hi
    simpa [mem_epigraph_iff] using hξ i hi
  have hsum_mem :
      (∑ i ∈ s, α i • (x i, ξ i)) ∈ epigraph f :=
    hconv.sum_mem hα_nonneg hα_sum hmem
  -- Expanding the product-space weighted sum exposes the desired first and second coordinates.
  rw [mem_epigraph_iff] at hsum_mem
  simpa [Prod.fst_sum, Prod.snd_sum, Prod.smul_mk, smul_eq_mul, mul_comm, mul_left_comm,
    mul_assoc] using hsum_mem

/-- Helper for Corrollary 8.12: if one weighted point has value `-∞`, convexity of the epigraph
forces the whole finite barycenter to have value `-∞`. -/
private lemma weighted_sum_value_eq_bot_of_mem_bot_of_convex_epigraph (f : H → EReal)
    (hconv : Convex ℝ (epigraph f)) {ι : Type v} (s : Finset ι) (α : ι → ℝ) (x : ι → H)
    {k : ι} (hk : k ∈ s) (hbot : f (x k) = ⊥) (hα_nonneg : ∀ i ∈ s, 0 ≤ α i)
    (hαk_pos : 0 < α k) (hα_sum : ∑ i ∈ s, α i = 1) (hdom : ∀ i ∈ s, x i ∈ dom f) :
    f (∑ i ∈ s, α i • x i) = ⊥ := by
  classical
  -- Drive the weighted epigraph height below every real bound by lowering the distinguished point.
  refine (EReal.eq_bot_iff_forall_lt _).2 ?_
  intro r
  have hrest :
      ∀ i ∈ s.erase k, ∃ ξ : ℝ, f (x i) ≤ (ξ : EReal) := by
    intro i hi
    exact exists_real_ge_of_mem_dom f (hdom i (Finset.mem_of_mem_erase hi))
  let ξ : ι → ℝ := fun i ↦
    if hi : i ∈ s.erase k then Classical.choose (hrest i hi) else 0
  let t : ℝ := ∑ i ∈ s.erase k, α i * ξ i
  let η : ℝ := (r - t) / α k - 1
  let ξ' : ι → ℝ := fun i ↦ if i = k then η else ξ i
  have hξ' : ∀ i ∈ s, f (x i) ≤ (ξ' i : EReal) := by
    intro i hi
    by_cases hik : i = k
    · -- At the distinguished index, every real height lies above `-∞`.
      subst hik
      rw [hbot]
      simp [ξ']
    · -- Away from `k`, use the chosen finite epigraph witnesses from the effective domain.
      have hi_erase : i ∈ s.erase k := by
        simp [Finset.mem_erase, hik, hi]
      have hξi : f (x i) ≤ (ξ i : EReal) := by
        have hξ_eq : ξ i = Classical.choose (hrest i hi_erase) := by
          dsimp [ξ]
          rw [dif_pos hi_erase]
        rw [hξ_eq]
        exact Classical.choose_spec (hrest i hi_erase)
      simpa [ξ', hik] using hξi
  have hsum_le :
      f (∑ i ∈ s, α i • x i) ≤ ((∑ i ∈ s, α i * ξ' i : ℝ) : EReal) :=
    weighted_sum_mem_epigraph_of_convex_epigraph f hconv s α x ξ'
      hα_nonneg hα_sum hξ'
  have hsum_real :
      ∑ i ∈ s, α i * ξ' i = α k * η + t := by
    -- Isolate the distinguished index from the remaining finite sum.
    have htail :
        ∑ i ∈ s.erase k, α i * ξ' i = ∑ i ∈ s.erase k, α i * ξ i := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hik : i ≠ k := Finset.ne_of_mem_erase hi
      simp [ξ', hik]
    calc
      ∑ i ∈ s, α i * ξ' i = α k * ξ' k + ∑ i ∈ s \ ({k} : Finset ι), α i * ξ' i := by
        exact Finset.sum_eq_add_sum_diff_singleton_of_mem hk (f := fun i ↦ α i * ξ' i)
      _ = α k * ξ' k + ∑ i ∈ s.erase k, α i * ξ' i := by
        rw [Finset.sdiff_singleton_eq_erase]
      _ = α k * η + ∑ i ∈ s.erase k, α i * ξ i := by
        rw [htail]
        simp [ξ']
      _ = α k * η + t := by
        rfl
  have hη_eq : α k * η + t = r - α k := by
    -- The chosen height makes the total weighted height strictly smaller than `r`.
    dsimp [η]
    field_simp [hαk_pos.ne']
    ring
  have hheight_lt : ((∑ i ∈ s, α i * ξ' i : ℝ) : EReal) < (r : EReal) := by
    rw [hsum_real, hη_eq]
    exact EReal.coe_lt_coe_iff.mpr (sub_lt_self _ hαk_pos)
  exact lt_of_le_of_lt hsum_le hheight_lt

/-- Helper for Corrollary 8.12: if all weighted values are finite and non-`⊥`, the epigraph
barycenter argument rewrites to the finite Jensen inequality. -/
private lemma finite_jensen_of_convex_epigraph_of_ne_bot (f : H → EReal)
    (hconv : Convex ℝ (epigraph f)) {ι : Type v} (s : Finset ι) (α : ι → ℝ) (x : ι → H)
    (hα_nonneg : ∀ i ∈ s, 0 ≤ α i) (hα_sum : ∑ i ∈ s, α i = 1)
    (hdom : ∀ i ∈ s, x i ∈ dom f) (hne_bot : ∀ i ∈ s, f (x i) ≠ ⊥) :
    f (∑ i ∈ s, α i • x i) ≤ ∑ i ∈ s, (α i : EReal) * f (x i) := by
  classical
  let ξ : ι → ℝ := fun i ↦ (f (x i)).toReal
  have hξ : ∀ i ∈ s, f (x i) ≤ (ξ i : EReal) := by
    -- Finite values admit their canonical real representatives via `toReal`.
    intro i hi
    exact EReal.le_coe_toReal (ne_of_lt ((mem_dom_iff f (x i)).mp (hdom i hi)))
  have hreal_le :
      f (∑ i ∈ s, α i • x i) ≤ ((∑ i ∈ s, α i * ξ i : ℝ) : EReal) :=
    weighted_sum_mem_epigraph_of_convex_epigraph f hconv s α x ξ hα_nonneg hα_sum hξ
  have hsum_eq :
      ((∑ i ∈ s, α i * ξ i : ℝ) : EReal) =
        ∑ i ∈ s, (α i : EReal) * f (x i) := by
    -- Without any `⊥` values, every summand is the cast of the corresponding real product.
    revert hdom hne_bot
    refine Finset.induction_on s ?_ ?_
    · intro _ _
      simp
    · intro i s hi ih hdom hne_bot
      have hdom_s : ∀ j ∈ s, x j ∈ dom f := by
        intro j hj
        exact hdom j (Finset.mem_insert_of_mem hj)
      have hne_bot_s : ∀ j ∈ s, f (x j) ≠ ⊥ := by
        intro j hj
        exact hne_bot j (Finset.mem_insert_of_mem hj)
      have htop_i : f (x i) ≠ ⊤ := ne_of_lt ((mem_dom_iff f (x i)).mp
        (hdom i (Finset.mem_insert_self i s)))
      have hbot_i : f (x i) ≠ ⊥ := hne_bot i (Finset.mem_insert_self i s)
      simp [hi, ξ, ih hdom_s hne_bot_s, EReal.coe_add, EReal.coe_mul,
        EReal.coe_toReal htop_i hbot_i]
  exact hreal_le.trans_eq hsum_eq

/-- Helper for Corrollary 8.12: convexity of the epigraph implies the finite Jensen inequality for
positive coefficients summing to `1`. -/
private lemma finite_jensen_on_dom_of_convex_epigraph (f : H → EReal)
    (hconv : Convex ℝ (epigraph f)) {ι : Type v} (s : Finset ι) (α : ι → ℝ) (x : ι → H)
    (hα : ∀ i ∈ s, α i ∈ Set.Ioo (0 : ℝ) 1) (hα_sum : ∑ i ∈ s, α i = 1)
    (hdom : ∀ i ∈ s, x i ∈ dom f) :
    f (∑ i ∈ s, α i • x i) ≤ ∑ i ∈ s, (α i : EReal) * f (x i) := by
  by_cases hbot : ∃ i ∈ s, f (x i) = ⊥
  · rcases hbot with ⟨k, hk, hk_bot⟩
    have hleft_bot :
        f (∑ i ∈ s, α i • x i) = ⊥ :=
      weighted_sum_value_eq_bot_of_mem_bot_of_convex_epigraph f hconv s α x hk hk_bot
        (fun i hi ↦ (hα i hi).1.le) (hα k hk).1 hα_sum hdom
    have hright_bot :
        ∑ i ∈ s, (α i : EReal) * f (x i) = ⊥ := by
      -- A positive coefficient multiplying a `-∞` value forces the whole sum to be `-∞`.
      exact
        (WithBot.sum_eq_bot_iff
          (s := s) (f := fun i ↦ ((α i : EReal) * f (x i)))).2 <| by
            refine ⟨k, hk, ?_⟩
            have hαkE : 0 < (α k : EReal) := EReal.coe_pos.mpr (hα k hk).1
            simpa [hk_bot] using (EReal.mul_bot_of_pos hαkE)
    simp [hleft_bot, hright_bot]
  · have hne_bot : ∀ i ∈ s, f (x i) ≠ ⊥ := by
      intro i hi
      exact fun hi_bot ↦ hbot ⟨i, hi, hi_bot⟩
    -- Once the `⊥` case is excluded, the finite epigraph barycenter proof rewrites directly.
    exact finite_jensen_of_convex_epigraph_of_ne_bot f hconv s α x
      (fun i hi ↦ (hα i hi).1.le) hα_sum hdom hne_bot

-- Proof sketch: combine Proposition 8.4 with the endpoint cases `α = 0` and `α = 1`; for
-- coefficients in `]0,1[`, use the open-interval Jensen formulation, while at the endpoints the
-- desired inequality is immediate from the affine combination.
/-- The textbook binary Jensen inequality on the closed interval `[0,1]` is equivalent to
convexity of the epigraph. -/
theorem convex_epigraph_iff_closedSegment_jensen (f : H → EReal) :
    Convex ℝ (epigraph f) ↔
      ∀ x y : H, ∀ α : ℝ, α ∈ Set.Icc (0 : ℝ) 1 →
        x ∈ dom f → y ∈ dom f →
        f (α • x + (1 - α) • y) ≤
          (α : EReal) * f x + (((1 - α : ℝ) : EReal) * f y) := by
  constructor
  · intro hconv x y α hα hx hy
    rcases hα with ⟨hα_nonneg, hα_le_one⟩
    by_cases hα0 : α = 0
    · -- At `α = 0`, the affine combination collapses to the right endpoint.
      subst hα0
      simp
    by_cases hα1 : α = 1
    · -- At `α = 1`, the affine combination collapses to the left endpoint.
      subst hα1
      simp
    -- Away from the endpoints, Proposition 8.4 gives the open-segment Jensen inequality.
    have hα_pos : 0 < α := lt_of_le_of_ne hα_nonneg (Ne.symm hα0)
    have hα_lt_one : α < 1 := lt_of_le_of_ne hα_le_one hα1
    exact (convex_epigraph_iff_jensen_on_dom f).1 hconv hx hy hα_pos hα_lt_one
  · intro hclosed
    refine (convex_epigraph_iff_jensen_on_dom f).2 ?_
    intro x y hx hy α hα_pos hα_lt_one
    -- The closed-segment formulation applies in particular to coefficients in `]0,1[`.
    exact hclosed x y α ⟨le_of_lt hα_pos, le_of_lt hα_lt_one⟩ hx hy

/-- Helper for Corrollary 8.12: the finite Jensen inequality specialized to a two-point family
recovers the open-segment Jensen inequality. -/
private lemma openSegment_jensen_of_finset_jensen (f : H → EReal)
    (hfin :
      ∀ {ι : Type v} (s : Finset ι) (α : ι → ℝ) (x : ι → H),
        (∀ i ∈ s, α i ∈ Set.Ioo (0 : ℝ) 1) →
        (∑ i ∈ s, α i = 1) →
        (∀ i ∈ s, x i ∈ dom f) →
          f (∑ i ∈ s, α i • x i) ≤
            ∑ i ∈ s, (α i : EReal) * f (x i))
    {x y : H} {α : ℝ} (hα : α ∈ Set.Ioo (0 : ℝ) 1) (hx : x ∈ dom f) (hy : y ∈ dom f) :
    f (α • x + (1 - α) • y) ≤
      (α : EReal) * f x + (((1 - α : ℝ) : EReal) * f y) := by
  let w : ULift.{v, 0} (Fin 2) → ℝ := fun i ↦ ![α, 1 - α] i.down
  let z : ULift.{v, 0} (Fin 2) → H := fun i ↦ ![x, y] i.down
  have hw_mem : ∀ i ∈ (Finset.univ : Finset (ULift.{v, 0} (Fin 2))), w i ∈ Set.Ioo (0 : ℝ) 1 := by
    intro i _
    rcases i with ⟨i⟩
    fin_cases i
    · simpa [w] using hα
    · dsimp [w]
      constructor
      · exact sub_pos.mpr hα.2
      · linarith [hα.1]
  have hw_sum : ∑ i ∈ (Finset.univ : Finset (ULift.{v, 0} (Fin 2))), w i = 1 := by
    -- Transport the `ULift (Fin 2)` sum back to `Fin 2` and evaluate it there.
    calc
      ∑ i ∈ (Finset.univ : Finset (ULift.{v, 0} (Fin 2))), w i =
          ∑ i : ULift.{v, 0} (Fin 2), w i := by
        simp
      _ = ∑ j : Fin 2, w ⟨j⟩ := by
        exact
          (Equiv.sum_comp ((Equiv.ulift : ULift.{v, 0} (Fin 2) ≃ Fin 2).symm) w).symm
      _ = 1 := by
        simp [w, Fin.sum_univ_two]
  have hz_dom : ∀ i ∈ (Finset.univ : Finset (ULift.{v, 0} (Fin 2))), z i ∈ dom f := by
    intro i _
    rcases i with ⟨i⟩
    fin_cases i
    · simpa [z] using hx
    · simpa [z] using hy
  have htwo :=
    hfin (ι := ULift.{v, 0} (Fin 2))
      (Finset.univ : Finset (ULift.{v, 0} (Fin 2))) w z hw_mem hw_sum hz_dom
  have hsum_left :
      (∑ i ∈ (Finset.univ : Finset (ULift.{v, 0} (Fin 2))), w i • z i) =
        α • x + (1 - α) • y := by
    -- The two-point barycenter is exactly the affine combination from the statement.
    calc
      ∑ i ∈ (Finset.univ : Finset (ULift.{v, 0} (Fin 2))), w i • z i =
          ∑ i : ULift.{v, 0} (Fin 2), w i • z i := by
        simp
      _ = ∑ j : Fin 2, w ⟨j⟩ • z ⟨j⟩ := by
        exact
          (Equiv.sum_comp ((Equiv.ulift : ULift.{v, 0} (Fin 2) ≃ Fin 2).symm)
            (fun i ↦ w i • z i)).symm
      _ = α • x + (1 - α) • y := by
        simp [w, z, Fin.sum_univ_two]
  have hsum_right :
      (∑ i ∈ (Finset.univ : Finset (ULift.{v, 0} (Fin 2))), (w i : EReal) * f (z i)) =
        (α : EReal) * f x + (((1 - α : ℝ) : EReal) * f y) := by
    -- The two-term weighted value sum simplifies to the desired right-hand side.
    calc
      ∑ i ∈ (Finset.univ : Finset (ULift.{v, 0} (Fin 2))), (w i : EReal) * f (z i) =
          ∑ i : ULift.{v, 0} (Fin 2), (w i : EReal) * f (z i) := by
        simp
      _ = ∑ j : Fin 2, (w ⟨j⟩ : EReal) * f (z ⟨j⟩) := by
        exact
          (Equiv.sum_comp ((Equiv.ulift : ULift.{v, 0} (Fin 2) ≃ Fin 2).symm)
            (fun i ↦ (w i : EReal) * f (z i))).symm
      _ = (α : EReal) * f x + (((1 - α : ℝ) : EReal) * f y) := by
        simp [w, z, Fin.sum_univ_two]
  -- Simplifying the specialized finite-family inequality gives the binary Jensen inequality.
  simpa [hsum_left, hsum_right] using htwo

-- Proof sketch: use Proposition 8.11 for the equivalence between convexity and the finite Jensen
-- inequality on `dom f`. Specializing the finite-family clause to a two-point family gives the
-- open-interval Jensen inequality, and Proposition 8.4 recovers convexity from that two-point
-- formulation.
/-- Corrollary 8.12: the canonical convexity condition `Convex ℝ (epigraph f)`, the finite Jensen
inequality for positive coefficients in `]0,1[` summing to `1`, and the two-point Jensen
inequality for coefficients in `]0,1[` are equivalent formulations of convexity for an
extended-real-valued function. -/
theorem tfae_convex_epigraph_finset_jensen_openSegment_jensen (f : H → EReal) :
    List.TFAE [
      Convex ℝ (epigraph f),
      ∀ {ι : Type v} (s : Finset ι) (α : ι → ℝ) (x : ι → H),
        (∀ i ∈ s, α i ∈ Set.Ioo (0 : ℝ) 1) →
        (∑ i ∈ s, α i = 1) →
        (∀ i ∈ s, x i ∈ dom f) →
          f (∑ i ∈ s, α i • x i) ≤
            ∑ i ∈ s, (α i : EReal) * f (x i),
      ∀ x y : H, ∀ α : ℝ, α ∈ Set.Ioo (0 : ℝ) 1 →
        x ∈ dom f → y ∈ dom f →
        f (α • x + (1 - α) • y) ≤
          (α : EReal) * f x + (((1 - α : ℝ) : EReal) * f y)
    ] := by
  tfae_have 1 → 2 := by
    intro hconv ι s α x hα hs hx
    -- Convexity gives the finite Jensen inequality through the epigraph barycenter argument.
    exact finite_jensen_on_dom_of_convex_epigraph f hconv s α x hα hs hx
  tfae_have 2 → 3 := by
    intro hfin x y α hα hx hy
    -- Specializing the finite-family inequality to two points recovers the open-segment form.
    exact openSegment_jensen_of_finset_jensen f hfin hα hx hy
  tfae_have 3 → 1 := by
    intro hopen
    -- Proposition 8.4 turns the open-segment Jensen inequality back into convexity.
    exact (convex_epigraph_iff_jensen_on_dom f).2 <| by
      intro x y hx hy α hα_pos hα_lt_one
      exact hopen x y α ⟨hα_pos, hα_lt_one⟩ hx hy
  tfae_finish

end ERealFunction

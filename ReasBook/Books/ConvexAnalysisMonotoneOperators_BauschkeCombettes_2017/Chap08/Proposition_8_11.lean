/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Proposition_8_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace ERealFunction

variable {H : Type u} [AddCommGroup H] [Module ℝ H]

omit [AddCommGroup H] [Module ℝ H] in
/-- Helper for Proposition 8.11: every point in the effective domain admits a real height lying
above the function value. -/
private lemma exists_real_ge_of_mem_dom (f : H → EReal) {x : H} (hx : x ∈ dom f) :
    ∃ ξ : ℝ, f x ≤ (ξ : EReal) := by
  -- Domain membership means that the value lies strictly below `+∞`, so a real separator exists.
  rw [mem_dom_iff] at hx
  rcases EReal.lt_iff_exists_real_btwn.mp hx with ⟨ξ, hξ, _⟩
  exact ⟨ξ, le_of_lt hξ⟩

/-- Helper for Proposition 8.11: convexity of the epigraph preserves finite weighted barycenters
of real-height epigraph points. -/
private lemma weighted_sum_mem_epigraph_of_convex_epigraph (f : H → EReal)
    (hconv : Convex ℝ (epigraph f)) {ι : Type v} (t : Finset ι) (w : ι → ℝ) (x : ι → H)
    (ξ : ι → ℝ) (hw₀ : ∀ i ∈ t, 0 ≤ w i) (hw₁ : ∑ i ∈ t, w i = 1)
    (hξ : ∀ i ∈ t, f (x i) ≤ (ξ i : EReal)) :
    f (∑ i ∈ t, w i • x i) ≤ ((∑ i ∈ t, w i * ξ i : ℝ) : EReal) := by
  have hmem : ∀ i ∈ t, (x i, ξ i) ∈ epigraph f := by
    -- Each chosen real height places the corresponding point in the epigraph.
    intro i hi
    simpa [mem_epigraph_iff] using hξ i hi
  have hsum_mem :
      (∑ i ∈ t, w i • (x i, ξ i)) ∈ epigraph f :=
    hconv.sum_mem hw₀ hw₁ hmem
  -- Expanding the product-space weighted sum exposes the desired first and second coordinates.
  rw [mem_epigraph_iff] at hsum_mem
  simpa [Prod.fst_sum, Prod.snd_sum, Prod.smul_mk, smul_eq_mul, mul_comm, mul_left_comm,
    mul_assoc] using hsum_mem

/-- Helper for Proposition 8.11: if one weighted point has value `-∞`, convexity of the epigraph
forces the whole finite barycenter to have value `-∞`. -/
private lemma weighted_sum_value_eq_bot_of_mem_bot_of_convex_epigraph (f : H → EReal)
    (hconv : Convex ℝ (epigraph f)) {ι : Type v} (t : Finset ι) (w : ι → ℝ) (x : ι → H)
    {k : ι} (hk : k ∈ t) (hbot : f (x k) = ⊥) (hw₀ : ∀ i ∈ t, 0 ≤ w i) (hwk : 0 < w k)
    (hw₁ : ∑ i ∈ t, w i = 1) (hdom : ∀ i ∈ t, x i ∈ dom f) :
    f (∑ i ∈ t, w i • x i) = ⊥ := by
  classical
  -- Route correction: the distinguished `-∞` point does not admit a canonical finite height, so we
  -- instead drive the total real epigraph height below every prescribed real bound.
  refine (EReal.eq_bot_iff_forall_lt _).2 ?_
  intro r
  have hrest :
      ∀ i ∈ t.erase k, ∃ ξ : ℝ, f (x i) ≤ (ξ : EReal) := by
    intro i hi
    exact exists_real_ge_of_mem_dom f (hdom i (Finset.mem_of_mem_erase hi))
  let ξ : ι → ℝ := fun i ↦
    if hi : i ∈ t.erase k then Classical.choose (hrest i hi) else 0
  let s : ℝ := ∑ i ∈ t.erase k, w i * ξ i
  let η : ℝ := (r - s) / w k - 1
  let ξ' : ι → ℝ := fun i ↦ if i = k then η else ξ i
  have hξ' : ∀ i ∈ t, f (x i) ≤ (ξ' i : EReal) := by
    intro i hi
    by_cases hik : i = k
    · -- At the distinguished index, any real height lies above `-∞`.
      subst hik
      rw [hbot]
      simp [ξ']
    · -- Away from `k`, use the chosen finite epigraph witnesses from the effective domain.
      have hi_erase : i ∈ t.erase k := by
        simp [Finset.mem_erase, hik, hi]
      have hξi : f (x i) ≤ (ξ i : EReal) := by
        have hξ_eq : ξ i = Classical.choose (hrest i hi_erase) := by
          dsimp [ξ]
          rw [dif_pos hi_erase]
        rw [hξ_eq]
        exact Classical.choose_spec (hrest i hi_erase)
      simpa [ξ', hik] using hξi
  have hsum_le :
      f (∑ i ∈ t, w i • x i) ≤ ((∑ i ∈ t, w i * ξ' i : ℝ) : EReal) :=
    weighted_sum_mem_epigraph_of_convex_epigraph f hconv t w x ξ'
      hw₀ hw₁ hξ'
  have hsum_real :
      ∑ i ∈ t, w i * ξ' i = w k * η + s := by
    -- Isolate the distinguished index from the remaining finite sum.
    have htail :
        ∑ x ∈ t.erase k, w x * ξ' x = ∑ x ∈ t.erase k, w x * ξ x := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hik : i ≠ k := Finset.ne_of_mem_erase hi
      simp [ξ', hik]
    calc
      ∑ i ∈ t, w i * ξ' i = w k * ξ' k + ∑ x ∈ t \ ({k} : Finset ι), w x * ξ' x := by
        exact Finset.sum_eq_add_sum_diff_singleton_of_mem hk (f := fun i ↦ w i * ξ' i)
      _ = w k * ξ' k + ∑ x ∈ t.erase k, w x * ξ' x := by
        rw [Finset.sdiff_singleton_eq_erase]
      _ = w k * η + ∑ x ∈ t.erase k, w x * ξ x := by
        rw [htail]
        simp [ξ']
      _ = w k * η + s := by
        rfl
  have hη_eq : w k * η + s = r - w k := by
    -- The definition of `η` was chosen to place the total height strictly below `r`.
    dsimp [η]
    field_simp [hwk.ne']
    ring
  have hheight_lt : ((∑ i ∈ t, w i * ξ' i : ℝ) : EReal) < (r : EReal) := by
    rw [hsum_real, hη_eq]
    exact EReal.coe_lt_coe_iff.mpr (sub_lt_self _ hwk)
  exact lt_of_le_of_lt hsum_le hheight_lt

/-- Helper for Proposition 8.11: when all function values are finite and non-`⊥`, the finite
epigraph barycenter argument rewrites directly to the desired Jensen inequality. -/
private lemma finite_jensen_of_convex_epigraph_of_ne_bot (f : H → EReal)
    (hconv : Convex ℝ (epigraph f)) {ι : Type v} (t : Finset ι) (w : ι → ℝ) (x : ι → H)
    (hw₀ : ∀ i ∈ t, 0 ≤ w i) (hw₁ : ∑ i ∈ t, w i = 1)
    (hdom : ∀ i ∈ t, x i ∈ dom f) (hne_bot : ∀ i ∈ t, f (x i) ≠ ⊥) :
    f (∑ i ∈ t, w i • x i) ≤ ∑ i ∈ t, (w i : EReal) * f (x i) := by
  classical
  let ξ : ι → ℝ := fun i ↦ (f (x i)).toReal
  have hξ : ∀ i ∈ t, f (x i) ≤ (ξ i : EReal) := by
    -- Finite values admit their canonical real representatives via `toReal`.
    intro i hi
    exact EReal.le_coe_toReal (ne_of_lt ((mem_dom_iff f (x i)).mp (hdom i hi)))
  have hreal_le :
      f (∑ i ∈ t, w i • x i) ≤ ((∑ i ∈ t, w i * ξ i : ℝ) : EReal) :=
    weighted_sum_mem_epigraph_of_convex_epigraph f hconv t w x ξ hw₀ hw₁ hξ
  have hsum_eq :
      ((∑ i ∈ t, w i * ξ i : ℝ) : EReal) =
        ∑ i ∈ t, (w i : EReal) * f (x i) := by
    -- With no `⊥` values and no `⊤` values on the domain, each term is the cast of a real product.
    classical
    revert hdom hne_bot
    refine Finset.induction_on t ?_ ?_
    · intro _ _
      simp
    · intro i t hi ih hdom hne_bot
      have hdom_t : ∀ j ∈ t, x j ∈ dom f := by
        intro j hj
        exact hdom j (Finset.mem_insert_of_mem hj)
      have hne_bot_t : ∀ j ∈ t, f (x j) ≠ ⊥ := by
        intro j hj
        exact hne_bot j (Finset.mem_insert_of_mem hj)
      have htop_i : f (x i) ≠ ⊤ := ne_of_lt ((mem_dom_iff f (x i)).mp
        (hdom i (Finset.mem_insert_self i t)))
      have hbot_i : f (x i) ≠ ⊥ := hne_bot i (Finset.mem_insert_self i t)
      simp [hi, ξ, ih hdom_t hne_bot_t, EReal.coe_add, EReal.coe_mul,
        EReal.coe_toReal htop_i hbot_i]
  exact hreal_le.trans_eq hsum_eq

/-- Helper for Proposition 8.11: the finite-family Jensen hypothesis specializes to the two-point
Jensen inequality used in Proposition 8.4. -/
private lemma two_point_jensen_of_finite_jensen (f : H → EReal)
    (hfin :
      ∀ {ι : Type v} (t : Finset ι) (w : ι → ℝ) (x : ι → H),
        (∀ i ∈ t, 0 < w i) →
        (∑ i ∈ t, w i = 1) →
        (∀ i ∈ t, x i ∈ dom f) →
        f (∑ i ∈ t, w i • x i) ≤
          ∑ i ∈ t, (w i : EReal) * f (x i))
    {x y : H} (hx : x ∈ dom f) (hy : y ∈ dom f) {α : ℝ} (hα : 0 < α)
    (hα_lt_one : α < 1) :
    f (α • x + (1 - α) • y) ≤
      (α : EReal) * f x + (((1 - α : ℝ) : EReal) * f y) := by
  let w : ULift.{v, 0} (Fin 2) → ℝ := fun i ↦ ![α, 1 - α] i.down
  let z : ULift.{v, 0} (Fin 2) → H := fun i ↦ ![x, y] i.down
  have hw_pos : ∀ i ∈ (Finset.univ : Finset (ULift.{v, 0} (Fin 2))), 0 < w i := by
    intro i _
    rcases i with ⟨i⟩
    fin_cases i <;> simp [w, hα, sub_pos.mpr hα_lt_one]
  have hw_sum : ∑ i ∈ (Finset.univ : Finset (ULift.{v, 0} (Fin 2))), w i = 1 := by
    -- Transport the finite sum over `ULift (Fin 2)` back to `Fin 2`.
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
      (Finset.univ : Finset (ULift.{v, 0} (Fin 2))) w z hw_pos hw_sum hz_dom
  have hsum_left :
      (∑ i : ULift.{v, 0} (Fin 2), w i • z i) = α • x + (1 - α) • y := by
    have hleft_ulift :
        (∑ i : ULift.{v, 0} (Fin 2), w i • z i) = ∑ j : Fin 2, w ⟨j⟩ • z ⟨j⟩ := by
      exact
        (Equiv.sum_comp ((Equiv.ulift : ULift.{v, 0} (Fin 2) ≃ Fin 2).symm)
          (fun i ↦ w i • z i)).symm
    exact hleft_ulift.trans <| by simp [w, z, Fin.sum_univ_two]
  have hsum_right :
      (∑ i : ULift.{v, 0} (Fin 2), (w i : EReal) * f (z i)) =
        (α : EReal) * f x + (((1 - α : ℝ) : EReal) * f y) := by
    have hright_ulift :
        (∑ i : ULift.{v, 0} (Fin 2), (w i : EReal) * f (z i)) =
          ∑ j : Fin 2, (w ⟨j⟩ : EReal) * f (z ⟨j⟩) := by
      exact
        (Equiv.sum_comp ((Equiv.ulift : ULift.{v, 0} (Fin 2) ≃ Fin 2).symm)
          (fun i ↦ (w i : EReal) * f (z i))).symm
    exact hright_ulift.trans <| by simp [w, z, Fin.sum_univ_two]
  -- Simplifying the two-index family recovers the standard binary Jensen inequality.
  simpa [hsum_left, hsum_right] using htwo

-- Proof sketch: for the forward implication, view each `(x i, f (x i))` as a point of
-- `epigraph f` and apply the finite weighted-sum characterization of convexity for that epigraph;
-- the second coordinate gives the desired inequality. For the reverse implication, specialize the
-- finite-family hypothesis to a two-point index set with weights `α` and `1 - α`, then invoke
-- Proposition 8.4.
/-- Proposition 8.11: an extended-real-valued function is convex if and only if every finite convex
combination of effective-domain points with positive coefficients summing to `1` satisfies
Jensen's inequality. -/
theorem convex_epigraph_iff_finite_jensen_on_dom (f : H → EReal) :
    Convex ℝ (epigraph f) ↔
      ∀ {ι : Type v} (t : Finset ι) (w : ι → ℝ) (x : ι → H),
        (∀ i ∈ t, 0 < w i) →
        (∑ i ∈ t, w i = 1) →
        (∀ i ∈ t, x i ∈ dom f) →
        f (∑ i ∈ t, w i • x i) ≤
          ∑ i ∈ t, (w i : EReal) * f (x i) := by
  constructor
  · intro hconv ι t w x hw_pos hw_sum hdom
    by_cases hbot : ∃ i ∈ t, f (x i) = ⊥
    · rcases hbot with ⟨k, hk, hk_bot⟩
      have hleft_bot :
          f (∑ i ∈ t, w i • x i) = ⊥ :=
        weighted_sum_value_eq_bot_of_mem_bot_of_convex_epigraph f hconv t w x hk hk_bot
          (fun i hi ↦ (hw_pos i hi).le) (hw_pos k hk) hw_sum hdom
      have hright_bot :
          ∑ i ∈ t, (w i : EReal) * f (x i) = ⊥ := by
        -- A positive weight multiplying a `-∞` value makes the whole sum equal to `-∞`.
        exact
          (WithBot.sum_eq_bot_iff
            (s := t) (f := fun i ↦ ((w i : EReal) * f (x i)))).2 <| by
              refine ⟨k, hk, ?_⟩
              have hwkE : 0 < (w k : EReal) := EReal.coe_pos.mpr (hw_pos k hk)
              simpa [hk_bot] using (EReal.mul_bot_of_pos hwkE)
      simp [hleft_bot, hright_bot]
    · have hne_bot : ∀ i ∈ t, f (x i) ≠ ⊥ := by
        intro i hi
        exact fun hi_bot ↦ hbot ⟨i, hi, hi_bot⟩
      -- Once the `⊥` case is excluded, the finite epigraph barycenter proof rewrites directly.
      exact finite_jensen_of_convex_epigraph_of_ne_bot f hconv t w x
        (fun i hi ↦ (hw_pos i hi).le) hw_sum hdom hne_bot
  · intro hfin
    -- The reverse direction reduces to the two-point Jensen criterion from Proposition 8.4.
    exact (convex_epigraph_iff_jensen_on_dom f).2 <| by
      intro x y hx hy α hα hα_lt_one
      exact two_point_jensen_of_finite_jensen f hfin hx hy hα hα_lt_one

end ERealFunction

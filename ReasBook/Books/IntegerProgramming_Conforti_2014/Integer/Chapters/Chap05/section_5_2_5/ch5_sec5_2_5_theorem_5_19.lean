/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Order.PiLex
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_2_4.ch5_sec5_2_4_definition_5_2_4_extra_1

-- Domain-style sampling for this refine pass:
-- * primary domain: stage-indexed lexicographic cutting-plane algorithms for pure integer programs
-- * source-facing/core owner: `GomoryLexicographicCuttingPlaneMethod`
-- * nearby owner patterns inspected:
--   `PeriodicGomoryFractionalCuttingPlaneMethod.toGomoryLexicographicCuttingPlaneMethod`,
--   `MixedIntegerGomoryLexicographicCuttingPlaneMethod.toGomoryLexicographicCuttingPlaneMethod`,
--   and `EllipsoidFeasibilityMethod.StopsAt`
-- * primitive data: the stagewise iterate, stopping-row selector, and cut/relaxation data
-- * derived API: `StopsAt`, `stopsAt_iff`, and the finiteness/termination consequences

-- Declarations for this item will be appended below by the statement pipeline.

section Theorem519

/-- A stage-indexed execution of Gomory's lexicographic cutting plane method for a bounded pure
integer program. At stage `t`, the iterate `iterates t` records the lexicographically optimal
tableau solution `(x̄₀ᵗ, …, x̄ₙᵗ)`, `selectedRow t` is the tableau row used to generate the next
Gomory cut, `relaxation t` is the current stage relaxation in the original decision variables, and
`cutColumns t`, `cutCoeff t`, `cutRhs t` record the Gomory fractional cut that is appended at a
nonterminal stage. -/
structure GomoryLexicographicCuttingPlaneMethod (n : ℕ) where
  feasibleRegion : Set (Fin (n + 1) → ℝ)
  bounded_feasibleRegion : Bornology.IsBounded feasibleRegion
  relaxation : ℕ → Set (Fin n → ℝ)
  iterates : ℕ → Fin (n + 1) → ℝ
  iterates_mem_feasibleRegion : ∀ t : ℕ, iterates t ∈ feasibleRegion
  iterates_mem_relaxation : ∀ t : ℕ, (fun j ↦ iterates t j.succ) ∈ relaxation t
  selectedRow : ℕ → Option (Fin (n + 1))
  selectedRow_none_iff :
    ∀ t : ℕ, selectedRow t = none ↔
      ∀ k : Fin (n + 1), iterates t k ∈ Set.range (Int.cast : ℤ → ℝ)
  cutColumns : ℕ → Finset (Fin n)
  cutCoeff : ℕ → Fin n → ℚ
  cutRhs : ℕ → ℚ
  relaxation_step :
    ∀ ⦃t : ℕ⦄ ⦃k : Fin (n + 1)⦄, selectedRow t = some k →
      relaxation (t + 1) =
        relaxation t ∩ gomory_fractional_cut (cutColumns t) (cutCoeff t) (cutRhs t)
  lexicographically_nonincreasing :
    ∀ t : ℕ, toLex (iterates (t + 1)) ≤ toLex (iterates t)
  selectedRow_spec :
    ∀ ⦃t : ℕ⦄ ⦃k : Fin (n + 1)⦄, selectedRow t = some k →
      (∀ i : Fin (n + 1), i < k → iterates t i ∈ Set.range (Int.cast : ℤ → ℝ)) ∧
        iterates t k ∉ Set.range (Int.cast : ℤ → ℝ)
  strict_progress_on_fractional_step :
    ∀ ⦃t : ℕ⦄ ⦃k : Fin (n + 1)⦄, selectedRow t = some k →
      toLex (iterates (t + 1)) < toLex (iterates t)
  selectedRow_eventually_forces_floor :
    ∀ ⦃t : ℕ⦄ ⦃k : Fin (n + 1)⦄,
      selectedRow t = some k →
      ∀ {m : ℤ},
      iterates t k < (m : ℝ) + 1 →
      (∀ i : Fin (n + 1), i < k →
        ∃ z : ℤ, ∀ s ≥ t + 1, iterates s i = (z : ℝ)) →
      ∀ s ≥ t + 1, iterates s k ≤ (m : ℝ)

namespace GomoryLexicographicCuttingPlaneMethod

/-- A run stops at stage `t` when no new tableau row is selected to generate a Gomory cut. -/
def StopsAt {n : ℕ} (A : GomoryLexicographicCuttingPlaneMethod n) (t : ℕ) : Prop :=
  A.selectedRow t = none

/-- A run stops exactly when the current tableau solution is integral in every coordinate. -/
@[simp] theorem stopsAt_iff
    {n : ℕ} (A : GomoryLexicographicCuttingPlaneMethod n) (t : ℕ) :
    A.StopsAt t ↔
      ∀ k : Fin (n + 1), A.iterates t k ∈ Set.range (Int.cast : ℤ → ℝ) :=
  A.selectedRow_none_iff t

/-- At every nonterminal stage, some fractional tableau row is selected for the next Gomory cut. -/
theorem exists_selectedRow_of_not_stopsAt
    {n : ℕ} (A : GomoryLexicographicCuttingPlaneMethod n) {t : ℕ}
    (ht : ¬ A.StopsAt t) :
    ∃ k : Fin (n + 1), A.selectedRow t = some k := by
  cases hrow : A.selectedRow t with
  | none =>
      exact False.elim (ht hrow)
  | some k =>
      exact ⟨k, rfl⟩

/-- At every nonterminal stage, the next relaxation is obtained by adjoining the recorded Gomory
fractional cut. -/
theorem relaxation_step_of_not_stopsAt
    {n : ℕ} (A : GomoryLexicographicCuttingPlaneMethod n) {t : ℕ}
    (ht : ¬ A.StopsAt t) :
    A.relaxation (t + 1) =
      A.relaxation t ∩ gomory_fractional_cut (A.cutColumns t) (A.cutCoeff t) (A.cutRhs t) := by
  obtain ⟨k, hk⟩ := A.exists_selectedRow_of_not_stopsAt ht
  exact A.relaxation_step hk

/-- At every nonterminal stage, the selected row witnesses the smallest fractional coordinate in
the current tableau solution. -/
theorem exists_selectedRow_spec_of_not_stopsAt
    {n : ℕ} (A : GomoryLexicographicCuttingPlaneMethod n) {t : ℕ}
    (ht : ¬ A.StopsAt t) :
    ∃ k : Fin (n + 1),
      (∀ i : Fin (n + 1), i < k → A.iterates t i ∈ Set.range (Int.cast : ℤ → ℝ)) ∧
        A.iterates t k ∉ Set.range (Int.cast : ℤ → ℝ) := by
  obtain ⟨k, hk⟩ := A.exists_selectedRow_of_not_stopsAt ht
  exact ⟨k, A.selectedRow_spec hk⟩

/-- At every nonterminal stage, the lexicographic tableau iterate decreases strictly. -/
theorem strict_progress_on_fractional_step_of_not_stopsAt
    {n : ℕ} (A : GomoryLexicographicCuttingPlaneMethod n) {t : ℕ}
    (ht : ¬ A.StopsAt t) :
    toLex (A.iterates (t + 1)) < toLex (A.iterates t) := by
  obtain ⟨k, hk⟩ := A.exists_selectedRow_of_not_stopsAt ht
  exact A.strict_progress_on_fractional_step hk

/-- Helper for Theorem 5.19: once every coordinate below `k` has stabilized, lexicographic
monotonicity turns the tail of the `k`th coordinate into an antitone sequence. -/
theorem coordinateAntitoneOfStablePrefix
    {n : ℕ} (A : GomoryLexicographicCuttingPlaneMethod n)
    {k : Fin (n + 1)} {T : ℕ}
    (hstable :
      ∀ i : Fin (n + 1), i < k → ∃ z : ℤ, ∀ s ≥ T, A.iterates s i = (z : ℝ)) :
    Antitone (fun u : ℕ ↦ A.iterates (T + u) k) := by
  -- Compare consecutive tail terms through the lexicographic order and the frozen lower prefix.
  refine antitone_nat_of_succ_le ?_
  intro u
  have hlex :
      toLex (A.iterates (T + (u + 1))) ≤ toLex (A.iterates (T + u)) := by
    simpa [Nat.add_assoc] using A.lexicographically_nonincreasing (T + u)
  refine Pi.apply_le_of_toLex hlex ?_
  intro j hj
  obtain ⟨z, hz⟩ := hstable j hj
  calc
    A.iterates (T + (u + 1)) j = (z : ℝ) := hz _ (by omega)
    _ = A.iterates (T + u) j := by
      symm
      exact hz _ (by omega)

/-- Helper for Theorem 5.19: if every coordinate below `k` is already a fixed integer and the
`k`th coordinate is still fractional, then the selected Gomory row must be `k`. -/
theorem selectedRowEqOfFractionalCoordinateOfStablePrefix
    {n : ℕ} (A : GomoryLexicographicCuttingPlaneMethod n)
    {k : Fin (n + 1)} {T t : ℕ}
    (hTt : T ≤ t)
    (hstable :
      ∀ i : Fin (n + 1), i < k → ∃ z : ℤ, ∀ s ≥ T, A.iterates s i = (z : ℝ))
    (hk_frac : A.iterates t k ∉ Set.range (Int.cast : ℤ → ℝ)) :
    A.selectedRow t = some k := by
  -- A fractional `k`th coordinate rules out termination at stage `t`.
  have hnotStop : ¬ A.StopsAt t := by
    intro ht
    exact hk_frac ((A.stopsAt_iff t).1 ht k)
  obtain ⟨r, hr⟩ := A.exists_selectedRow_of_not_stopsAt hnotStop
  -- The selected row cannot lie below or above `k`, so it must be exactly `k`.
  by_cases hrk : r = k
  · simpa [hrk] using hr
  · cases lt_or_gt_of_ne hrk with
    | inl hr_lt =>
        obtain ⟨z, hz⟩ := hstable r hr_lt
        have hr_int : A.iterates t r ∈ Set.range (Int.cast : ℤ → ℝ) := by
          exact ⟨z, (hz _ hTt).symm⟩
        exact False.elim ((A.selectedRow_spec hr).2 hr_int)
    | inr hk_lt =>
        exact False.elim (hk_frac ((A.selectedRow_spec hr).1 k hk_lt))

/-- Helper for Theorem 5.19: if every coordinate below `k` is eventually a fixed integer, then
the `k`th coordinate also eventually becomes a fixed integer. -/
theorem coordinateEventuallyIntegralAndConstantOfStablePrefix
    {n : ℕ} (A : GomoryLexicographicCuttingPlaneMethod n)
    {k : Fin (n + 1)} {T : ℕ}
    (hstable :
      ∀ i : Fin (n + 1), i < k → ∃ z : ℤ, ∀ s ≥ T, A.iterates s i = (z : ℝ)) :
    ∃ U : ℕ, T ≤ U ∧ ∃ z : ℤ, ∀ s ≥ U, A.iterates s k = (z : ℝ) := by
  -- First freeze the lower coordinates and read off antitonicity of the `k`th tail.
  let tail : ℕ → ℝ := fun u ↦ A.iterates (T + u) k
  have htail_antitone : Antitone tail :=
    A.coordinateAntitoneOfStablePrefix hstable
  obtain ⟨R, hball⟩ := A.bounded_feasibleRegion.subset_ball (A.iterates T)
  have hRpos : 0 < R := by
    have hcenter : A.iterates T ∈ Metric.ball (A.iterates T) R :=
      hball (A.iterates_mem_feasibleRegion T)
    simpa using hcenter
  have hlower_real : ∀ u : ℕ, A.iterates T k - R ≤ tail u := by
    intro u
    have hmem : A.iterates (T + u) ∈ Metric.ball (A.iterates T) R :=
      hball (A.iterates_mem_feasibleRegion (T + u))
    have hcoord_lt : dist (tail u) (A.iterates T k) < R := by
      exact (dist_pi_lt_iff hRpos).1 hmem k
    have hcoord_le : |tail u - A.iterates T k| ≤ R := le_of_lt (by
      simpa [tail, Real.dist_eq] using hcoord_lt)
    have hleft : -R ≤ tail u - A.iterates T k := (abs_le.mp hcoord_le).1
    simpa [tail, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      add_le_add_right hleft (A.iterates T k)
  let lower : ℤ := Int.floor (A.iterates T k - R)
  have hlower_int : ∀ u : ℕ, lower ≤ Int.floor (tail u) := by
    intro u
    exact Int.floor_mono (hlower_real u)
  have hfloor_antitone : Antitone (fun u : ℕ ↦ Int.floor (tail u)) := by
    intro u v huv
    exact Int.floor_mono (htail_antitone huv)
  let floorGap : ℕ → ℕ := fun u ↦ Int.toNat (Int.floor (tail u) - lower)
  have hfloorGap_antitone : Antitone floorGap := by
    intro u v huv
    dsimp [floorGap]
    have hu : lower ≤ Int.floor (tail u) := hlower_int u
    have hv : lower ≤ Int.floor (tail v) := hlower_int v
    have huv' : Int.floor (tail v) ≤ Int.floor (tail u) := hfloor_antitone huv
    omega
  -- The floor tail lives in a bounded antitone sequence of naturals, so it eventually freezes.
  obtain ⟨u0, hu0⟩ := WellFoundedLT.antitone_chain_condition hfloorGap_antitone
  let m : ℤ := Int.floor (tail u0)
  have hfloor_const : ∀ u ≥ u0, Int.floor (tail u) = m := by
    intro u hu
    have hu_eq : floorGap u0 = floorGap u := hu0 u hu
    dsimp [floorGap] at hu_eq
    have hu0_lower : lower ≤ Int.floor (tail u0) := hlower_int u0
    have hu_lower : lower ≤ Int.floor (tail u) := hlower_int u
    dsimp [m]
    omega
  let U := T + u0
  -- If the first floor-stable iterate is already integral, the coordinate is fixed immediately.
  by_cases hU_int : A.iterates U k ∈ Set.range (Int.cast : ℤ → ℝ)
  · rcases hU_int with ⟨z, hzU⟩
    have hm_eq_z : m = z := by
      calc
        m = Int.floor (A.iterates U k) := by
          simp [m, U, tail]
        _ = Int.floor (z : ℝ) := by rw [hzU]
        _ = z := Int.floor_intCast z
    refine ⟨U, by omega, z, ?_⟩
    intro s hs
    have hTs : T ≤ s := le_trans (by omega) hs
    have hs_ge_u0 : u0 ≤ s - T := by omega
    have hfloor_s : Int.floor (A.iterates s k) = m := by
      have hs' := hfloor_const (s - T) hs_ge_u0
      simpa [m, tail, Nat.add_sub_of_le hTs] using hs'
    have hle_s : A.iterates s k ≤ (z : ℝ) := by
      have hs' := htail_antitone hs_ge_u0
      simpa [tail, U, hzU, Nat.add_sub_of_le hTs] using hs'
    have hge_s : (z : ℝ) ≤ A.iterates s k := by
      have hfloor_le := Int.floor_le (A.iterates s k)
      rw [hfloor_s, hm_eq_z] at hfloor_le
      exact hfloor_le
    exact le_antisymm hle_s hge_s
  · -- Otherwise the selected row is exactly `k`, so the cut forces all later values down to the
    -- frozen floor, and the constant floor value upgrades this to equality.
    have hrow : A.selectedRow U = some k :=
      A.selectedRowEqOfFractionalCoordinateOfStablePrefix
        (T := T) (t := U) (by omega) hstable hU_int
    have hbelow_m_plus_one : A.iterates U k < (m : ℝ) + 1 := by
      dsimp [m, U, tail]
      exact Int.lt_floor_add_one (tail u0)
    have hforce :
        ∀ s ≥ U + 1, A.iterates s k ≤ (m : ℝ) := by
      apply A.selectedRow_eventually_forces_floor hrow hbelow_m_plus_one
      intro i hi
      obtain ⟨z, hz⟩ := hstable i hi
      exact ⟨z, fun s hs ↦ hz s (by omega)⟩
    refine ⟨U + 1, by omega, m, ?_⟩
    intro s hs
    have hTs : T ≤ s := le_trans (by omega) hs
    have hs_ge_u0 : u0 ≤ s - T := by omega
    have hfloor_s : Int.floor (A.iterates s k) = m := by
      have hs' := hfloor_const (s - T) hs_ge_u0
      simpa [m, tail, Nat.add_sub_of_le hTs] using hs'
    have hle_s : A.iterates s k ≤ (m : ℝ) := hforce s hs
    have hge_s : (m : ℝ) ≤ A.iterates s k := by
      simpa [hfloor_s] using Int.floor_le (A.iterates s k)
    exact le_antisymm hle_s hge_s

/-- Helper for Theorem 5.19: every initial coordinate block eventually stabilizes to one fixed
integer vector. -/
theorem prefixCoordinatesEventuallyIntegralAndConstant
    {n : ℕ} (A : GomoryLexicographicCuttingPlaneMethod n)
    (k : Fin (n + 1)) :
    ∃ T : ℕ, ∀ i : Fin (n + 1), i ≤ k → ∃ z : ℤ, ∀ t ≥ T, A.iterates t i = (z : ℝ) := by
  refine Fin.induction ?_ ?_ k
  · -- The zero-th coordinate has no smaller coordinates, so the stabilization lemma applies
    -- directly with an empty prefix hypothesis.
    obtain ⟨T, -, z, hz⟩ :=
      A.coordinateEventuallyIntegralAndConstantOfStablePrefix
        (k := (0 : Fin (n + 1))) (T := 0) (by
          intro i hi
          exact False.elim (not_lt_of_ge (Fin.zero_le i) hi))
    refine ⟨T, ?_⟩
    intro i hi
    have hi_zero : i = 0 := le_antisymm hi (Fin.zero_le i)
    subst hi_zero
    exact ⟨z, hz⟩
  · intro k ih
    rcases ih with ⟨T, hT⟩
    obtain ⟨U, hTU, z, hz⟩ :=
      A.coordinateEventuallyIntegralAndConstantOfStablePrefix
        (k := k.succ) (T := T) (by
          intro i hi
          exact hT i ((Fin.le_castSucc_iff).2 hi))
    refine ⟨U, ?_⟩
    intro i hi
    by_cases hik : i = k.succ
    · subst hik
      exact ⟨z, hz⟩
    · have hi_lt : i < k.succ := lt_of_le_of_ne hi hik
      obtain ⟨zi, hzi⟩ := hT i ((Fin.le_castSucc_iff).2 hi_lt)
      exact ⟨zi, fun t ht ↦ hzi t (le_trans hTU ht)⟩

/-- The lexicographic Gomory iterate sequence takes only finitely many values. -/
theorem finite_iterates
    {n : ℕ} (A : GomoryLexicographicCuttingPlaneMethod n) :
    Set.Finite (Set.range A.iterates) := by
  -- Route correction: first freeze the full coordinate vector, then restrict the range to a
  -- finite initial segment of stages.
  obtain ⟨T, hT⟩ := A.prefixCoordinatesEventuallyIntegralAndConstant (Fin.last n)
  have hconst : ∀ t ≥ T, A.iterates t = A.iterates T := by
    intro t ht
    funext i
    obtain ⟨z, hz⟩ := hT i (Fin.le_last i)
    rw [hz t ht, hz T le_rfl]
  refine (Set.finite_range (fun s : Fin (T + 1) ↦ A.iterates s)).subset ?_
  rintro _ ⟨t, rfl⟩
  by_cases ht : t ≤ T
  · exact ⟨⟨t, Nat.lt_succ_of_le ht⟩, rfl⟩
  · refine ⟨⟨T, Nat.lt_succ_self T⟩, ?_⟩
    symm
    exact hconst t (by omega)

end GomoryLexicographicCuttingPlaneMethod

/-- Each coordinate of the lexicographic Gomory iterate sequence eventually becomes integral and
then remains unchanged. -/
theorem gomory_lexicographic_coordinate_eventually_integral_and_constant
    {n : ℕ} (A : GomoryLexicographicCuttingPlaneMethod n) :
    ∀ k : Fin (n + 1), ∃ T : ℕ, ∀ t ≥ T,
      A.iterates t k ∈ Set.range (Int.cast : ℤ → ℝ) ∧
        A.iterates (t + 1) k = A.iterates t k := by
  intro k
  -- Specialize the prefix-stabilization statement to the chosen coordinate.
  obtain ⟨T, hT⟩ := A.prefixCoordinatesEventuallyIntegralAndConstant k
  obtain ⟨z, hz⟩ := hT k le_rfl
  refine ⟨T, ?_⟩
  intro t ht
  constructor
  · exact ⟨z, (hz t ht).symm⟩
  · rw [hz (t + 1) (by omega), hz t ht]

/-- Theorem 5.19. Gomory's lexicographic cutting plane method terminates in a finite number of
iterations. -/
theorem gomory_lexicographic_cutting_plane_method_terminates
    {n : ℕ} (A : GomoryLexicographicCuttingPlaneMethod n) :
    ∃ T : ℕ, A.StopsAt T := by
  -- Once every coordinate has stabilized to an integer, the stopping criterion becomes immediate.
  obtain ⟨T, hT⟩ := A.prefixCoordinatesEventuallyIntegralAndConstant (Fin.last n)
  refine ⟨T, ?_⟩
  rw [A.stopsAt_iff]
  intro k
  obtain ⟨z, hz⟩ := hT k (Fin.le_last k)
  exact ⟨z, (hz T le_rfl).symm⟩

end Theorem519
